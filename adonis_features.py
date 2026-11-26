import io
import json
import math
import re
import threading
import time

from PIL import Image, ImageDraw, ImageFont
import requests

from adonis_config import (
    category_by_score,
    get_gender_config,
    normalize_gender,
)


class CryptoPayClient:
    def __init__(self, token="", testnet=False):
        self.token = (token or "").strip()
        self.testnet = bool(testnet)
        self.base_url = (
            "https://testnet-pay.crypt.bot/api"
            if self.testnet
            else "https://pay.crypt.bot/api"
        )
        self._local = threading.local()

    def is_enabled(self):
        return bool(self.token)

    def _session(self):
        sess = getattr(self._local, "session", None)
        if sess is None:
            sess = requests.Session()
            self._local.session = sess
        return sess

    def _request(self, method_name, payload=None):
        if not self.token:
            return None, "CRYPTOBOT_TOKEN не настроен."
        url = f"{self.base_url}/{method_name}"
        headers = {
            "Crypto-Pay-API-Token": self.token,
            "Content-Type": "application/json",
        }
        try:
            resp = self._session().post(
                url,
                json=payload or {},
                headers=headers,
                timeout=(8, 20),
            )
            data = resp.json()
        except requests.exceptions.RequestException as err:
            return None, f"Сетевая ошибка CryptoBot: {type(err).__name__}"
        except ValueError:
            return None, f"Некорректный JSON от CryptoBot (HTTP {resp.status_code})"

        if not data.get("ok"):
            err_obj = data.get("error") or {}
            err_name = err_obj.get("name") or str(err_obj) or f"HTTP {resp.status_code}"
            return None, f"CryptoBot API: {err_name}"
        return data.get("result"), None

    def create_fiat_invoice(
        self,
        rub_amount,
        description,
        payload="",
        expires_in=1800,
        paid_btn_name=None,
        paid_btn_url=None,
    ):
        body = {
            "currency_type": "fiat",
            "fiat": "RUB",
            "amount": f"{float(rub_amount):.2f}",
            "description": (description or "Оплата Adonis PSL")[:1024],
            "payload": (payload or "")[:4096],
            "expires_in": max(60, min(2678400, int(expires_in))),
            "allow_comments": False,
            "allow_anonymous": True,
        }
        if paid_btn_name and paid_btn_url:
            body["paid_btn_name"] = paid_btn_name
            body["paid_btn_url"] = paid_btn_url

        res, err = self._request("createInvoice", body)
        if err or not isinstance(res, dict):
            return None, err or "Пустой ответ от createInvoice."

        pay_url = (
            res.get("mini_app_invoice_url")
            or res.get("bot_invoice_url")
            or res.get("pay_url")
            or ""
        )
        return {
            "invoice_id": int(res["invoice_id"]),
            "status": res.get("status", "active"),
            "pay_url": pay_url,
            "mini_app_url": res.get("mini_app_invoice_url") or pay_url,
            "bot_url": res.get("bot_invoice_url") or pay_url,
            "raw": res,
        }, None

    def get_invoices(self, invoice_ids):
        if isinstance(invoice_ids, (list, tuple, set)):
            ids_str = ",".join(str(int(i)) for i in invoice_ids)
        else:
            ids_str = str(invoice_ids).strip()
        if not ids_str:
            return [], None

        res, err = self._request("getInvoices", {"invoice_ids": ids_str})
        if err:
            return None, err
        if isinstance(res, dict):
            return res.get("items", []), None
        if isinstance(res, list):
            return res, None
        return [], None

    def delete_invoice(self, invoice_id):
        res, err = self._request("deleteInvoice", {"invoice_id": int(invoice_id)})
        if err:
            return False, err
        return bool(res), None


class CryptoInvoicePoller:
    def __init__(
        self,
        client,
        fetch_active_fn,
        on_paid_fn,
        on_expired_fn,
        interval=25,
        log_fn=None,
    ):
        self.client = client
        self.fetch_active_fn = fetch_active_fn
        self.on_paid_fn = on_paid_fn
        self.on_expired_fn = on_expired_fn
        self.interval = max(10, int(interval))
        self.log_fn = log_fn or (lambda msg: print(f"[CryptoPoller] {msg}"))
        self._stop_evt = threading.Event()
        self._thread = None

    def start(self):
        if not self.client.is_enabled():
            return
        if self._thread and self._thread.is_alive():
            return
        self._thread = threading.Thread(
            target=self._loop,
            name="cryptobot-poller",
            daemon=True,
        )
        self._thread.start()

    def stop(self):
        self._stop_evt.set()

    def _loop(self):
        while not self._stop_evt.is_set():
            try:
                self._tick()
            except Exception as exc:
                self.log_fn(f"Ошибка цикла проверки счетов: {exc}")
            self._stop_evt.wait(self.interval)

    def _tick(self):
        active_rows = self.fetch_active_fn() or []
        if not active_rows:
            return

        now = int(time.time())
        id_to_exp = {int(inv_id): int(exp_at) for inv_id, exp_at in active_rows}
        all_ids = list(id_to_exp.keys())

        for start in range(0, len(all_ids), 50):
            batch = all_ids[start : start + 50]
            items, err = self.client.get_invoices(batch)
            if err or items is None:
                self.log_fn(f"getInvoices batch error: {err}")
                continue

            seen = set()
            for item in items:
                try:
                    inv_id = int(item["invoice_id"])
                except (KeyError, TypeError, ValueError):
                    continue
                seen.add(inv_id)
                st = (item.get("status") or "").lower()
                if st == "paid":
                    self.on_paid_fn(inv_id, item)
                elif st == "expired":
                    self.on_expired_fn(inv_id)

            for inv_id in batch:
                if inv_id not in seen and id_to_exp.get(inv_id, 0) > 0 and now > id_to_exp[inv_id] + 120:
                    self.on_expired_fn(inv_id)


def serialize_metrics(
    gender,
    final_score,
    category,
    verdict,
    params_dict,
    symmetry_pct=None,
    face_shape="",
):
    payload = {
        "gender": normalize_gender(gender),
        "final_score": round(float(final_score), 1) if final_score is not None else 0.0,
        "category": category or "",
        "verdict": verdict or "",
        "params": {k: round(float(v), 1) for k, v in (params_dict or {}).items()},
        "symmetry_pct": round(float(symmetry_pct), 1) if symmetry_pct is not None else None,
        "face_shape": face_shape or "",
    }
    return json.dumps(payload, ensure_ascii=False)


def deserialize_metrics(metrics_json):
    if not metrics_json:
        return None
    try:
        data = json.loads(metrics_json)
        if isinstance(data, dict) and data.get("params") and data.get("final_score"):
            return data
    except Exception:
        pass
    return None


def extract_metrics_fallback(scores_text, gender="m"):
    if not scores_text:
        return None
    g = normalize_gender(gender)
    cfg = get_gender_config(g)
    params = {}

    for label, patterns in cfg["param_rules"]:
        for pat in patterns:
            m = re.search(
                rf"(?im)^[\s•\-]*(?:\d+[.)]\s*)?{pat}[^0-9\n]*?(\d+(?:[.,]\d+)?)\s*/\s*8",
                scores_text,
            )
            if m:
                try:
                    params[label] = round(max(1.0, min(8.0, float(m.group(1).replace(",", ".")))), 1)
                    break
                except ValueError:
                    continue

    m_score = re.search(r"Итоговая оценка[^0-9\n]*?(\d+(?:[.,]\d+)?)\s*/\s*8", scores_text, flags=re.IGNORECASE)
    if m_score:
        final_score = round(max(1.0, min(8.0, float(m_score.group(1).replace(",", ".")))), 1)
    elif params:
        w_sum = sum(v * cfg["param_weights"].get(k, 0.05) for k, v in params.items())
        w_tot = sum(cfg["param_weights"].get(k, 0.05) for k in params)
        final_score = round(w_sum / max(1e-6, w_tot), 1)
    else:
        return None

    m_cat = re.search(r"(?im)^Категория[:\s]+(.+)$", scores_text)
    category = m_cat.group(1).strip() if m_cat else category_by_score(final_score, gender=g)

    m_verd = re.search(r"(?im)^Вердикт[:\s]+(.+)$", scores_text)
    verdict = m_verd.group(1).strip()[:170] if m_verd else ""

    return {
        "gender": g,
        "final_score": final_score,
        "category": category,
        "verdict": verdict,
        "params": params,
        "symmetry_pct": None,
        "face_shape": "",
    }


def compute_battle_result(metrics1, metrics2, gender="m"):
    g = normalize_gender(gender)
    cfg = get_gender_config(g)
    ordered_labels = [label for label, _ in cfg["param_rules"]]

    p1 = metrics1.get("params") or {}
    p2 = metrics2.get("params") or {}
    s1 = round(float(metrics1.get("final_score") or 0.0), 1)
    s2 = round(float(metrics2.get("final_score") or 0.0), 1)

    rounds = []
    wins1, wins2 = 0, 0
    for label in ordered_labels:
        v1 = round(float(p1.get(label, s1)), 1)
        v2 = round(float(p2.get(label, s2)), 1)
        diff = round(v1 - v2, 1)
        if diff > 0.01:
            r_win = 1
            wins1 += 1
        elif diff < -0.01:
            r_win = 2
            wins2 += 1
        else:
            r_win = 0
        rounds.append(
            {
                "name": label,
                "v1": v1,
                "v2": v2,
                "diff": diff,
                "winner": r_win,
            }
        )

    score_diff = round(abs(s1 - s2), 1)
    if s1 > s2 + 0.01:
        overall_winner = 1
    elif s2 > s1 + 0.01:
        overall_winner = 2
    else:
        overall_winner = 0

    return {
        "gender": g,
        "score1": s1,
        "score2": s2,
        "cat1": metrics1.get("category") or category_by_score(s1, gender=g),
        "cat2": metrics2.get("category") or category_by_score(s2, gender=g),
        "winner": overall_winner,
        "score_diff": score_diff,
        "wins1": wins1,
        "wins2": wins2,
        "rounds": rounds,
    }


def _fallback_get_font(size, bold=False):
    try:
        return ImageFont.load_default(size=size)
    except TypeError:
        return ImageFont.load_default()


def _calc_percentile(score):
    z = (float(score) - 3.95) / 0.95
    pct = 0.5 * (1.0 + math.erf(z / math.sqrt(2.0))) * 100.0
    return max(1, min(99, int(round(pct))))


def _wrap_text(draw, text, font, max_width, max_lines=3):
    words = (text or "").split()
    lines = []
    cur = ""
    truncated = False
    for word in words:
        cand = f"{cur} {word}".strip()
        if draw.textlength(cand, font=font) <= max_width:
            cur = cand
        else:
            if cur:
                lines.append(cur)
                if len(lines) >= max_lines:
                    truncated = True
                    cur = ""
                    break
            cur = word
    if cur and len(lines) < max_lines:
        lines.append(cur)
    elif cur:
        truncated = True

    if lines and (truncated or draw.textlength(lines[-1], font=font) > max_width):
        last = lines[-1].rstrip(" ,.;:-")
        while last and draw.textlength(last + "…", font=font) > max_width:
            last = last[:-1].rstrip(" ,.;:-")
        lines[-1] = (last + "…") if last else "…"
    return lines


def _crop_portrait_rect(image_bytes, target_w, target_h, radius=20, face_bbox=None):
    with io.BytesIO(image_bytes) as bio, Image.open(bio) as src:
        img = src.convert("RGBA")
        w, h = img.size
        target_ratio = target_w / float(target_h)

        if face_bbox:
            x0, y0, x1, y1 = face_bbox
            fcx = (x0 + x1) * 0.5 * w
            fcy = (y0 + y1) * 0.48 * h
            face_w = (x1 - x0) * w
            face_h = (y1 - y0) * h
            crop_h = min(h, max(face_h * 2.15, face_w * 2.0 / max(0.3, target_ratio), h * 0.55))
            crop_w = crop_h * target_ratio
            if crop_w > w:
                crop_w = w
                crop_h = crop_w / target_ratio
        else:
            if (w / float(h)) > target_ratio:
                crop_h = h
                crop_w = crop_h * target_ratio
            else:
                crop_w = w
                crop_h = crop_w / target_ratio
            fcx, fcy = w * 0.5, h * 0.44

        left = max(0.0, min(w - crop_w, fcx - crop_w * 0.5))
        top = max(0.0, min(h - crop_h, fcy - crop_h * 0.46))
        box = (int(left), int(top), int(left + crop_w), int(top + crop_h))
        cropped = img.crop(box).resize((target_w, target_h), Image.Resampling.LANCZOS)

        mask = Image.new("L", (target_w, target_h), 0)
        ImageDraw.Draw(mask).rounded_rectangle((0, 0, target_w, target_h), radius=radius, fill=255)
        out = Image.new("RGBA", (target_w, target_h), (0, 0, 0, 0))
        out.paste(cropped, (0, 0), mask)
        return out


def _draw_pill(draw, x, y, w, h, text, font, bg, border, fg):
    draw.rounded_rectangle((x, y, x + w, y + h), radius=h // 2, fill=bg, outline=border, width=2)
    bb = draw.textbbox((0, 0), text, font=font)
    tw, th = bb[2] - bb[0], bb[3] - bb[1]
    draw.text((x + (w - tw) / 2, y + (h - th) / 2 - bb[1]), text, font=font, fill=fg)


def _draw_ring(draw, cx, cy, radius, ratio, center_txt, label_txt, accent, get_font):
    ratio = max(0.0, min(1.0, float(ratio)))
    bbox = (cx - radius, cy - radius, cx + radius, cy + radius)
    draw.arc(bbox, start=0, end=360, fill=(30, 38, 56, 255), width=9)
    if ratio > 0.01:
        draw.arc(bbox, start=-90, end=-90 + int(360 * ratio), fill=accent, width=9)

    f_val = get_font(26 if len(center_txt) <= 5 else 20, bold=True)
    vb = draw.textbbox((0, 0), center_txt, font=f_val)
    vw, vh = vb[2] - vb[0], vb[3] - vb[1]
    draw.text((cx - vw / 2, cy - vh / 2 - vb[1]), center_txt, font=f_val, fill=(248, 250, 252, 255))

    f_lbl = get_font(16, bold=False)
    lb = draw.textbbox((0, 0), label_txt, font=f_lbl)
    lw = lb[2] - lb[0]
    draw.text((cx - lw / 2, cy + radius + 16), label_txt, font=f_lbl, fill=(148, 163, 184, 255))


def _draw_gradient_pill(base_img, x, y, w, h, c_left, c_right, radius=24):
    grad = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    gdraw = ImageDraw.Draw(grad)
    for col in range(w):
        t = col / max(1.0, float(w - 1))
        r = int(c_left[0] + (c_right[0] - c_left[0]) * t)
        g = int(c_left[1] + (c_right[1] - c_left[1]) * t)
        b = int(c_left[2] + (c_right[2] - c_left[2]) * t)
        gdraw.line((col, 0, col, h), fill=(r, g, b, 255))

    mask = Image.new("L", (w, h), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, w - 1, h - 1), radius=radius, fill=255)
    pill = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    pill.paste(grad, (0, 0), mask)
    base_img.alpha_composite(pill, (int(x), int(y)))


def _draw_crown(base_img, cx, cy, size=88, tilt_deg=14):
    cw, ch = int(size * 1.4), int(size * 1.1)
    layer = Image.new("RGBA", (cw, ch), (0, 0, 0, 0))
    cdraw = ImageDraw.Draw(layer)

    pts = [
        (cw * 0.14, ch * 0.78),
        (cw * 0.08, ch * 0.30),
        (cw * 0.33, ch * 0.54),
        (cw * 0.50, ch * 0.16),
        (cw * 0.67, ch * 0.54),
        (cw * 0.92, ch * 0.30),
        (cw * 0.86, ch * 0.78),
    ]
    cdraw.polygon(pts, fill=(250, 204, 21, 255), outline=(180, 125, 12, 255))
    cdraw.rounded_rectangle(
        (cw * 0.14, ch * 0.74, cw * 0.86, ch * 0.88),
        radius=6,
        fill=(234, 179, 8, 255),
        outline=(161, 98, 7, 255),
        width=2,
    )
    for px, py in ((cw * 0.08, ch * 0.28), (cw * 0.50, ch * 0.14), (cw * 0.92, ch * 0.28)):
        r = size * 0.075
        cdraw.ellipse((px - r, py - r, px + r, py + r), fill=(254, 240, 138, 255), outline=(180, 125, 12, 255))
    gems = [
        (cw * 0.32, ch * 0.68, (59, 130, 246, 255)),
        (cw * 0.50, ch * 0.64, (244, 63, 94, 255)),
        (cw * 0.68, ch * 0.68, (16, 185, 129, 255)),
    ]
    for gx, gy, gcol in gems:
        gr = size * 0.06
        cdraw.ellipse((gx - gr, gy - gr, gx + gr, gy + gr), fill=gcol)

    rotated = layer.rotate(tilt_deg, resample=Image.Resampling.BICUBIC, expand=True)
    rw, rh = rotated.size
    base_img.alpha_composite(rotated, (int(cx - rw / 2), int(cy - rh / 2)))


def _draw_dual_radar(base_img, cx, cy, radius, axes_labels, vals1, vals2, get_font):
    overlay = Image.new("RGBA", base_img.size, (0, 0, 0, 0))
    odraw = ImageDraw.Draw(overlay)
    n = len(axes_labels)
    if n < 3:
        return base_img

    for frac in (0.25, 0.50, 0.75, 1.0):
        ring_pts = [
            (
                cx + radius * frac * math.cos(-math.pi / 2 + 2 * math.pi * i / n),
                cy + radius * frac * math.sin(-math.pi / 2 + 2 * math.pi * i / n),
            )
            for i in range(n)
        ]
        odraw.polygon(ring_pts, outline=(38, 47, 68, 210))

    f_lbl = get_font(17, bold=False)
    pts1, pts2 = [], []
    for i, label in enumerate(axes_labels):
        ang = -math.pi / 2 + 2 * math.pi * i / n
        cos_a, sin_a = math.cos(ang), math.sin(ang)
        odraw.line((cx, cy, cx + radius * cos_a, cy + radius * sin_a), fill=(38, 47, 68, 190), width=1)

        f1 = max(0.12, min(1.0, float(vals1[i]) / 8.0))
        f2 = max(0.12, min(1.0, float(vals2[i]) / 8.0))
        pts1.append((cx + radius * f1 * cos_a, cy + radius * f1 * sin_a))
        pts2.append((cx + radius * f2 * cos_a, cy + radius * f2 * sin_a))

        bb = odraw.textbbox((0, 0), label, font=f_lbl)
        lw, lh = bb[2] - bb[0], bb[3] - bb[1]
        lx = cx + (radius + 24) * cos_a
        ly = cy + (radius + 24) * sin_a
        if cos_a < -0.30:
            tx = lx - lw
        elif cos_a > 0.30:
            tx = lx
        else:
            tx = lx - lw / 2
        ty = ly - lh / 2 - bb[1]
        odraw.text((tx, ty), label, font=f_lbl, fill=(148, 163, 184, 255))

    odraw.polygon(pts2, fill=(244, 63, 94, 66), outline=(251, 113, 133, 240))
    for px, py in pts2:
        odraw.ellipse((px - 4, py - 4, px + 4, py + 4), fill=(251, 113, 133, 255))

    odraw.polygon(pts1, fill=(76, 141, 255, 66), outline=(96, 165, 250, 245))
    for px, py in pts1:
        odraw.ellipse((px - 4, py - 4, px + 4, py + 4), fill=(147, 197, 253, 255))

    return Image.alpha_composite(base_img, overlay)


def render_share_card(
    image_bytes,
    metrics,
    bot_username=None,
    geom=None,
    get_font_fn=None,
    crop_portrait_fn=None,
):
    get_font = get_font_fn or _fallback_get_font
    g = normalize_gender(metrics.get("gender", "m"))
    score = float(metrics.get("final_score") or 0.0)
    category = (metrics.get("category") or category_by_score(score, gender=g)).upper()
    verdict = (metrics.get("verdict") or "").strip()
    params = metrics.get("params") or {}
    sym_pct = metrics.get("symmetry_pct")
    face_shape = metrics.get("face_shape") or (geom.get("face_shape") if geom else "")

    W, H = 1080, 1350
    canvas = Image.new("RGBA", (W, H), (9, 11, 16, 255))
    draw = ImageDraw.Draw(canvas)

    f_brand = get_font(28, bold=True)
    f_tag = get_font(14, bold=True)
    f_wm = get_font(19, bold=False)
    draw.text((44, 38), "ADONIS PSL", font=f_brand, fill=(248, 250, 252, 255))

    badge_txt = "FEMALE CARD" if g == "f" else "BIOMETRIC CARD"
    badge_bg = (42, 24, 54, 255) if g == "f" else (20, 41, 74, 255)
    badge_bd = (116, 58, 152, 255) if g == "f" else (38, 79, 138, 255)
    badge_fg = (216, 180, 254, 255) if g == "f" else (96, 165, 250, 255)
    _draw_pill(draw, 252, 38, 168, 34, badge_txt, f_tag, badge_bg, badge_bd, badge_fg)

    wm = f"@{bot_username}" if bot_username else "ADONIS PSL BOT"
    wm_w = draw.textlength(wm, font=f_wm)
    draw.text((W - 44 - wm_w, 44), wm, font=f_wm, fill=(148, 163, 184, 255))

    draw.rounded_rectangle(
        (44, 102, W - 44, 594),
        radius=26,
        fill=(17, 20, 28, 255),
        outline=(32, 39, 54, 255),
        width=2,
    )

    if crop_portrait_fn is not None and image_bytes:
        portrait = crop_portrait_fn(image_bytes, 436, geom=geom)
    else:
        portrait = _crop_portrait_rect(
            image_bytes,
            436,
            436,
            radius=20,
            face_bbox=(geom.get("face_bbox") if geom else None),
        )
    canvas.alpha_composite(portrait, (72, 130))
    draw = ImageDraw.Draw(canvas)

    if face_shape:
        f_sh = get_font(16, bold=True)
        sw = int(draw.textlength(face_shape, font=f_sh)) + 32
        draw.rounded_rectangle(
            (88, 514, 88 + sw, 550),
            radius=18,
            fill=(10, 14, 22, 225),
            outline=(56, 70, 96, 230),
            width=1,
        )
        draw.text((104, 522), face_shape, font=f_sh, fill=(241, 245, 249, 255))

    rx = 544
    draw.text((rx, 132), "ОБЩАЯ ОЦЕНКА", font=get_font(16, bold=True), fill=(139, 149, 169, 255))

    f_big = get_font(96, bold=True)
    f_sl = get_font(40, bold=False)
    score_str = f"{score:.1f}"
    accent_main = (52, 211, 153, 255) if score >= 5.5 else (96, 165, 250, 255)
    draw.text((rx, 162), score_str, font=f_big, fill=(248, 250, 252, 255))
    sw_big = draw.textlength(score_str, font=f_big)
    draw.text((rx + sw_big + 8, 208), "/8", font=f_sl, fill=(100, 116, 139, 255))

    f_cat = get_font(20, bold=True)
    cw_pill = max(140, int(draw.textlength(category, font=f_cat)) + 44)
    _draw_pill(
        draw,
        rx,
        286,
        min(cw_pill, W - 72 - rx),
        44,
        category,
        f_cat,
        (20, 41, 74, 255) if score < 5.5 else (16, 52, 40, 255),
        (38, 79, 138, 255) if score < 5.5 else (26, 94, 68, 255),
        accent_main,
    )

    pct = _calc_percentile(score)
    draw.text(
        (rx, 352),
        f"Выше, чем у {pct} из 100",
        font=get_font(22, bold=True),
        fill=(96, 165, 250, 255),
    )

    v_text = verdict or "Биометрический индекс рассчитан по ключевым пропорциям и гармонии черт."
    f_verd = get_font(20, bold=False)
    for idx, line in enumerate(_wrap_text(draw, v_text, f_verd, max_width=(W - 76 - rx), max_lines=4)):
        draw.text((rx, 402 + idx * 30), line, font=f_verd, fill=(203, 213, 225, 255))

    draw.rounded_rectangle(
        (44, 622, W - 44, 860),
        radius=26,
        fill=(17, 20, 28, 255),
        outline=(32, 39, 54, 255),
        width=2,
    )
    draw.text((76, 646), "КЛЮЧЕВЫЕ ИНДЕКСЫ", font=get_font(15, bold=True), fill=(139, 149, 169, 255))

    skin_vals = [params[k] for k in ("Текстура кожи", "Тон кожи", "Тёмные круги") if k in params]
    skin_avg = sum(skin_vals) / len(skin_vals) if skin_vals else score
    harmony_val = float(params.get("Гармония", score))

    if sym_pct is not None:
        m1_val, m1_ratio, m1_lbl = f"{sym_pct:.0f}%", sym_pct / 100.0, "Симметрия"
    else:
        prop_val = float(params.get("Пропорции", score))
        m1_val, m1_ratio, m1_lbl = f"{prop_val:.1f}", prop_val / 8.0, "Пропорции"

    _draw_ring(draw, 226, 756, 56, m1_ratio, m1_val, m1_lbl, (76, 141, 255, 255), get_font)
    _draw_ring(draw, 540, 756, 56, skin_avg / 8.0, f"{skin_avg:.1f}", "Состояние кожи", (56, 189, 248, 255), get_font)
    _draw_ring(draw, 854, 756, 56, harmony_val / 8.0, f"{harmony_val:.1f}", "Гармония черт", (129, 140, 248, 255), get_font)

    draw.rounded_rectangle(
        (44, 888, W - 44, 1170),
        radius=26,
        fill=(17, 20, 28, 255),
        outline=(32, 39, 54, 255),
        width=2,
    )
    draw.text((76, 914), "ТОП-3 СИЛЬНЫЕ ЧЕРТЫ", font=get_font(15, bold=True), fill=(139, 149, 169, 255))

    ranked = sorted(
        [(k, float(v)) for k, v in params.items() if k != "Гармония"],
        key=lambda item: item[1],
        reverse=True,
    )[:3]
    if not ranked:
        ranked = [("Гармония", score)]

    f_tr_name = get_font(22, bold=True)
    f_tr_val = get_font(22, bold=True)
    ty = 964
    for idx, (t_name, t_val) in enumerate(ranked):
        rank_badge = f"#{idx + 1}"
        _draw_pill(
            draw,
            76,
            ty - 2,
            52,
            34,
            rank_badge,
            get_font(16, bold=True),
            (20, 41, 74, 255),
            (38, 79, 138, 255),
            (147, 197, 253, 255),
        )
        draw.text((146, ty), t_name, font=f_tr_name, fill=(235, 240, 248, 255))

        val_txt = f"{t_val:.1f}/8"
        vw = draw.textlength(val_txt, font=f_tr_val)
        draw.text((W - 76 - vw, ty), val_txt, font=f_tr_val, fill=(52, 211, 153, 255) if t_val >= 5.5 else (96, 165, 250, 255))

        bx0, bx1 = 440, W - 186
        draw.rounded_rectangle((bx0, ty + 10, bx1, ty + 22), radius=6, fill=(28, 35, 51, 255))
        fw = max(12, int((bx1 - bx0) * max(0.0, min(1.0, t_val / 8.0))))
        bcol = (52, 211, 153, 255) if t_val >= 5.5 else (76, 141, 255, 255)
        draw.rounded_rectangle((bx0, ty + 10, bx0 + fw, ty + 22), radius=6, fill=bcol)
        ty += 64

    _draw_gradient_pill(
        canvas,
        44,
        1202,
        W - 88,
        104,
        (37, 99, 235),
        (124, 58, 237) if g == "f" else (14, 165, 233),
        radius=26,
    )
    draw = ImageDraw.Draw(canvas)
    draw.text((82, 1222), "ПРОВЕРЬ СВОЮ ВНЕШНОСТЬ ПО ШКАЛЕ 1.0–8.0", font=get_font(17, bold=True), fill=(219, 234, 254, 255))
    draw.text((82, 1252), f"Telegram-бот:  {wm}", font=get_font(28, bold=True), fill=(255, 255, 255, 255))

    with io.BytesIO() as out_buf:
        canvas.convert("RGB").save(out_buf, format="JPEG", quality=92, subsampling=0)
        return out_buf.getvalue()


def render_battle_card(
    img1_bytes,
    img2_bytes,
    battle_data,
    metrics1,
    metrics2,
    bot_username=None,
    get_font_fn=None,
):
    get_font = get_font_fn or _fallback_get_font
    rounds = battle_data["rounds"]
    n_rows = len(rounds)

    BLUE = (76, 141, 255, 255)
    BLUE_LT = (96, 165, 250, 255)
    CORAL = (244, 63, 94, 255)
    CORAL_LT = (251, 113, 133, 255)
    WHITE = (248, 250, 252, 255)
    MUTED = (148, 163, 184, 255)

    W = 1000
    ry0 = 962
    rounds_box_h = 136 + n_rows * 66
    ry1 = ry0 + rounds_box_h
    rady0 = ry1 + 32
    rady1 = rady0 + 506
    fy = rady1 + 34
    H = fy + 104

    canvas = Image.new("RGBA", (W, H), (9, 11, 16, 255))
    draw = ImageDraw.Draw(canvas)

    f_title = get_font(48, bold=True)
    title_txt = "Баттл 1 на 1"
    tw = draw.textlength(title_txt, font=f_title)
    draw.text(((W - tw) / 2, 42), title_txt, font=f_title, fill=WHITE)

    f_sub = get_font(23, bold=False)
    sub_lines = [
        "Два фото — и разбор, кто выигрывает по",
        "чертам лица.",
    ]
    for i, sl in enumerate(sub_lines):
        sw = draw.textlength(sl, font=f_sub)
        draw.text(((W - sw) / 2, 112 + i * 32), sl, font=f_sub, fill=MUTED)

    p_w, p_h = 434, 468
    p1_x, p2_x, p_y = 48, W - 48 - p_w, 232

    f_flbl = get_font(24, bold=True)
    l1_w = draw.textlength("Боец 1", font=f_flbl)
    l2_w = draw.textlength("Боец 2", font=f_flbl)
    draw.text((p1_x + (p_w - l1_w) / 2, 192), "Боец 1", font=f_flbl, fill=BLUE_LT)
    draw.text((p2_x + (p_w - l2_w) / 2, 192), "Боец 2", font=f_flbl, fill=CORAL_LT)

    port1 = _crop_portrait_rect(img1_bytes, p_w, p_h, radius=24)
    port2 = _crop_portrait_rect(img2_bytes, p_w, p_h, radius=24)
    canvas.alpha_composite(port1, (p1_x, p_y))
    canvas.alpha_composite(port2, (p2_x, p_y))
    draw = ImageDraw.Draw(canvas)

    winner = battle_data["winner"]
    draw.rounded_rectangle(
        (p1_x, p_y, p1_x + p_w, p_y + p_h),
        radius=24,
        outline=BLUE if winner == 1 else (38, 46, 64, 255),
        width=4 if winner == 1 else 2,
    )
    draw.rounded_rectangle(
        (p2_x, p_y, p2_x + p_w, p_y + p_h),
        radius=24,
        outline=CORAL if winner == 2 else (38, 46, 64, 255),
        width=4 if winner == 2 else 2,
    )

    if winner == 1:
        _draw_crown(canvas, p1_x + p_w - 22, p_y + 16, size=86, tilt_deg=-18)
        draw = ImageDraw.Draw(canvas)
    elif winner == 2:
        _draw_crown(canvas, p2_x + 22, p_y + 16, size=86, tilt_deg=18)
        draw = ImageDraw.Draw(canvas)

    f_sc = get_font(56, bold=True)
    f_sc_sl = get_font(26, bold=False)
    f_cat = get_font(20, bold=True)

    for px_left, sc_val, cat_str, col in (
        (p1_x, battle_data["score1"], battle_data["cat1"].upper(), BLUE_LT),
        (p2_x, battle_data["score2"], battle_data["cat2"].upper(), CORAL_LT),
    ):
        s_txt = f"{sc_val:.1f}".replace(".", ",")
        sl_txt = "/8"
        total_w = draw.textlength(s_txt, font=f_sc) + draw.textlength(sl_txt, font=f_sc_sl) + 4
        sx = px_left + (p_w - total_w) / 2
        draw.text((sx, 718), s_txt, font=f_sc, fill=col)
        draw.text((sx + draw.textlength(s_txt, font=f_sc) + 4, 744), sl_txt, font=f_sc_sl, fill=MUTED)

        cw = draw.textlength(cat_str, font=f_cat)
        draw.text((px_left + (p_w - cw) / 2, 788), cat_str, font=f_cat, fill=WHITE)

    if winner == 1:
        badge_text = "Победа"
        b_bg, b_bd, b_fg = (18, 34, 62, 255), BLUE, BLUE_LT
        win_line = "Боец 1 побеждает"
        diff_line = f"Перевес +{battle_data['score_diff']:.1f}".replace(".", ",")
    elif winner == 2:
        badge_text = "Победа"
        b_bg, b_bd, b_fg = (62, 20, 32, 255), CORAL, CORAL_LT
        win_line = "Боец 2 побеждает"
        diff_line = f"Перевес +{battle_data['score_diff']:.1f}".replace(".", ",")
    else:
        badge_text = "Ничья"
        b_bg, b_bd, b_fg = (30, 38, 54, 255), (100, 116, 139, 255), WHITE
        win_line = "Равный итоговый балл"
        diff_line = f"Раунды {battle_data['wins1']} : {battle_data['wins2']}"

    _draw_pill(draw, (W - 224) // 2, 828, 224, 52, badge_text, get_font(24, bold=True), b_bg, b_bd, b_fg)

    f_wline = get_font(21, bold=True)
    f_dline = get_font(18, bold=False)
    wl_w = draw.textlength(win_line, font=f_wline)
    dl_w = draw.textlength(diff_line, font=f_dline)
    draw.text(((W - wl_w) / 2, 892), win_line, font=f_wline, fill=WHITE)
    draw.text(((W - dl_w) / 2, 920), diff_line, font=f_dline, fill=MUTED)

    draw.rounded_rectangle(
        (48, ry0, W - 48, ry1),
        radius=28,
        fill=(17, 20, 28, 255),
        outline=(30, 36, 51, 255),
        width=2,
    )

    draw.text((84, ry0 + 30), "Раунды по чертам", font=get_font(28, bold=True), fill=WHITE)

    f_cnt = get_font(34, bold=True)
    w1_s, sep_s, w2_s = str(battle_data["wins1"]), " : ", str(battle_data["wins2"])
    tot_cw = draw.textlength(w1_s, font=f_cnt) + draw.textlength(sep_s, font=f_cnt) + draw.textlength(w2_s, font=f_cnt)
    cx_cnt = W - 84 - tot_cw
    draw.text((cx_cnt, ry0 + 26), w1_s, font=f_cnt, fill=BLUE_LT)
    cx_cnt += draw.textlength(w1_s, font=f_cnt)
    draw.text((cx_cnt, ry0 + 26), sep_s, font=f_cnt, fill=MUTED)
    cx_cnt += draw.textlength(sep_s, font=f_cnt)
    draw.text((cx_cnt, ry0 + 26), w2_s, font=f_cnt, fill=CORAL_LT)

    f_hdr_sm = get_font(18, bold=True)
    draw.text((84, ry0 + 84), "Боец 1", font=f_hdr_sm, fill=BLUE_LT)
    r_lbl_w = draw.textlength("Боец 2", font=f_hdr_sm)
    draw.text((W - 84 - r_lbl_w, ry0 + 84), "Боец 2", font=f_hdr_sm, fill=CORAL_LT)

    f_rnum = get_font(22, bold=True)
    f_rname = get_font(20, bold=False)
    bar_x0, bar_x1 = 188, W - 188
    bar_mid = (bar_x0 + bar_x1) // 2
    half_w = (bar_x1 - bar_x0) // 2

    cur_y = ry0 + 124
    for r in rounds:
        s1_t = f"{r['v1']:.1f}".replace(".", ",")
        s2_t = f"{r['v2']:.1f}".replace(".", ",")
        draw.text((84, cur_y + 8), s1_t, font=f_rnum, fill=WHITE if r["winner"] == 1 else MUTED)
        s2_w = draw.textlength(s2_t, font=f_rnum)
        draw.text((W - 84 - s2_w, cur_y + 8), s2_t, font=f_rnum, fill=WHITE if r["winner"] == 2 else MUTED)

        nw = draw.textlength(r["name"], font=f_rname)
        draw.text((bar_mid - nw / 2, cur_y), r["name"], font=f_rname, fill=(226, 232, 240, 255))

        by0, by1 = cur_y + 32, cur_y + 44
        draw.rounded_rectangle((bar_x0, by0, bar_x1, by1), radius=6, fill=(28, 35, 51, 255))

        abs_diff = abs(r["diff"])
        if r["winner"] == 1 and abs_diff > 0:
            bw = max(14, int(half_w * min(1.0, abs_diff / 2.2)))
            draw.rounded_rectangle((bar_mid - bw, by0, bar_mid, by1), radius=6, fill=BLUE)
        elif r["winner"] == 2 and abs_diff > 0:
            bw = max(14, int(half_w * min(1.0, abs_diff / 2.2)))
            draw.rounded_rectangle((bar_mid, by0, bar_mid + bw, by1), radius=6, fill=CORAL)

        draw.line((bar_mid, by0 - 4, bar_mid, by1 + 4), fill=(148, 163, 184, 210), width=2)
        cur_y += 66

    draw.rounded_rectangle(
        (48, rady0, W - 48, rady1),
        radius=28,
        fill=(17, 20, 28, 255),
        outline=(30, 36, 51, 255),
        width=2,
    )
    draw.text((84, rady0 + 28), "Профиль черт", font=get_font(28, bold=True), fill=WHITE)

    leg_y = rady0 + 78
    draw.ellipse((86, leg_y + 5, 98, leg_y + 17), fill=BLUE_LT)
    draw.text((108, leg_y), "Боец 1", font=get_font(18, bold=True), fill=BLUE_LT)
    draw.ellipse((212, leg_y + 5, 224, leg_y + 17), fill=CORAL_LT)
    draw.text((234, leg_y), "Боец 2", font=get_font(18, bold=True), fill=CORAL_LT)

    radar_keys = [
        "Глаза",
        "Брови",
        "Губы",
        "Нос",
        "Пропорции",
        "Скулы",
        "Подбородок",
        "Текстура кожи",
        "Тон кожи",
        "Тёмные круги",
    ]
    p1 = metrics1.get("params") or {}
    p2 = metrics2.get("params") or {}
    vals1 = [float(p1.get(k, battle_data["score1"])) for k in radar_keys]
    vals2 = [float(p2.get(k, battle_data["score2"])) for k in radar_keys]

    canvas = _draw_dual_radar(
        canvas,
        W // 2,
        rady0 + 298,
        158,
        radar_keys,
        vals1,
        vals2,
        get_font,
    )
    draw = ImageDraw.Draw(canvas)

    tri = [(58, fy + 48), (82, fy + 10), (106, fy + 48)]
    draw.polygon(tri, fill=WHITE)

    wm = f"@{bot_username}" if bot_username else "ADONIS PSL"
    draw.text((124, fy + 4), "ADONIS PSL", font=get_font(28, bold=True), fill=WHITE)
    draw.text((124, fy + 38), wm, font=get_font(20, bold=False), fill=MUTED)

    btn_w, btn_h = 330, 68
    btn_x, btn_y = W - 48 - btn_w, fy - 2
    _draw_gradient_pill(canvas, btn_x, btn_y, btn_w, btn_h, (76, 141, 255), (244, 63, 94), radius=24)
    draw = ImageDraw.Draw(canvas)

    f_cta = get_font(22, bold=True)
    cta_txt = "Устрой свой баттл"
    cw_cta = draw.textlength(cta_txt, font=f_cta)
    draw.text((btn_x + (btn_w - cw_cta) / 2, btn_y + 20), cta_txt, font=f_cta, fill=WHITE)

    with io.BytesIO() as out_buf:
        canvas.convert("RGB").save(out_buf, format="JPEG", quality=92, subsampling=0)
        return out_buf.getvalue()