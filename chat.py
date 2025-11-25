# chat.py
"""
Invoice OCR + GST extractor (single-file)

Mode: Text-layer first -> High-accuracy OCR -> Fallback OCR -> Merge results
Auto scheduler: every 12 hours (first run immediately)
Stop: Type 'q' + ENTER anytime to stop the program immediately (even mid-processing).
"""

import os
import io
import re
import json
import sqlite3
import threading
import schedule
import time
import sys
from datetime import datetime
from typing import List, Tuple, Optional

from PIL import Image, ImageOps, ImageFilter
import fitz  # pymupdf
import pytesseract
from pytesseract import Output

# Optional OpenCV for stronger preprocessing (recommended)
try:
    import cv2
    import numpy as np
    OPENCV_AVAILABLE = True
except Exception:
    OPENCV_AVAILABLE = False

# Google libraries
import gspread
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload
from tabulate import tabulate
from pypdf import PdfReader
from dotenv import load_dotenv

# ---------------- CONFIG ----------------
# Tesseract command (change to your tesseract exe if needed)
pytesseract.pytesseract.tesseract_cmd = os.getenv(
    "TESSERACT_CMD", r"C:\Program Files\Tesseract-OCR\tesseract.exe"
)

# Flags and tuning
DEBUG_OCR = False                # prints intermediate OCR lines/tokens if True
HIGH_ACCURACY_DPI = 600         # DPI for high accuracy pass
FALLBACK_DPI = 300              # DPI for fallback pass
TESS_CONFIG_TEXT = r"--oem 3 --psm 6"     # line/paragraph mode
TESS_CONFIG_NUM  = r"--oem 3 --psm 6 -c tessedit_char_whitelist=0123456789.,₹RsINR"
AUTO_INFER_IGST_IF_MISSING = True  # if IGST missing and (Total - Taxable) >0, infer IGST

# Google drive/sheet - set in .env or edit here
load_dotenv()
SERVICE_ACCOUNT_FILE = os.getenv("SERVICE_ACCOUNT_FILE", "credentials.json")
INPUT_FOLDER_ID = os.getenv("INPUT_FOLDER_ID", "1XhSPOcqVBE4daUwChtvNyBrnfgC4oxmR")
PROCESSED_FOLDER_ID = os.getenv("PROCESSED_FOLDER_ID", "1vuWTZ39X4ShmtatYP5mBupYmXxw6YvUY")
SHEET_ID = os.getenv("SHEET_ID", "1Ky5h0ycJMrH0XCC94RfrdhAO2ypm6ceze6tVEdoy-FY")

# Azure OpenAI (optional) - keep if you have an Azure deployment key
AZURE_OPENAI_ENDPOINT = os.getenv("AZURE_OPENAI_ENDPOINT")
AZURE_OPENAI_KEY = os.getenv("AZURE_OPENAI_KEY")
AZURE_DEPLOYMENT = os.getenv("AZURE_OPENAI_DEPLOYMENT")

# ---------------- SETUP ----------------
# Google API setup
SCOPES = ["https://www.googleapis.com/auth/drive", "https://www.googleapis.com/auth/spreadsheets"]
creds = service_account.Credentials.from_service_account_file(SERVICE_ACCOUNT_FILE, scopes=SCOPES)
drive_service = build("drive", "v3", credentials=creds)
sheet_client = gspread.service_account(filename=SERVICE_ACCOUNT_FILE)

# SQLite DB
DB_FILE = "invoices_new.db"
conn = sqlite3.connect(DB_FILE, check_same_thread=False)
cur = conn.cursor()

COLUMNS = [
    "Date","Total_Amount","Invoice_Number","IRN",
    "Seller_Name","Seller_GSTIN_UIN","Seller_State_Name_Code",
    "Buyer_Name","Buyer_GSTIN_UIN","Buyer_State_Name_Code",
    "Buyer_Order_No","Destination","HSN_SAC",
    "IGST","CGST","SGST","Taxable_Value","Total_Tax_Amount",
    "Source_File","Upload_Date","Upload_Time"
]

COLUMN_TYPES = {c: "TEXT" for c in COLUMNS}
COLUMN_TYPES.update({
    "IGST":"NUMERIC","CGST":"NUMERIC","SGST":"NUMERIC",
    "Taxable_Value":"NUMERIC","Total_Tax_Amount":"NUMERIC","Total_Amount":"NUMERIC"
})
sql = ", ".join([f'"{c}" {COLUMN_TYPES[c]}' for c in COLUMNS])
cur.execute(f"CREATE TABLE IF NOT EXISTS invoices(id INTEGER PRIMARY KEY AUTOINCREMENT,{sql})")
conn.commit()

# ---------------- UTIL FUNCTIONS ----------------
def safe_float(x) -> float:
    """Robust numeric parse from OCR strings"""
    try:
        if x is None:
            return 0.0
        s = str(x).strip()
        s = s.replace("₹", "").replace("Rs.", "").replace("INR", "")
        s = s.replace(",", "").replace(" ", "")
        s = re.sub(r'[Oo]', '0', s)
        s = re.sub(r'[^0-9\-\.\+eE]', '', s)
        if s == "" or s == ".":
            return 0.0
        return float(s)
    except Exception:
        return 0.0

def extract_state_code_from_gstin(gstin: str) -> str:
    gstin = (gstin or "").strip()
    if len(gstin) >= 2 and gstin[:2].isdigit():
        return gstin[:2]
    return ""

GSTIN_STRICT = re.compile(r"\b\d{2}[A-Z]{5}\d{4}[A-Z]{1}[A-Z\d]{1}Z[A-Z\d]{1}\b", re.I)

def find_gstins_in_text(text: str) -> List[str]:
    joined = re.sub(r'[^0-9A-Za-z]', '', text).upper()
    found = GSTIN_STRICT.findall(joined)
    if not found:
        tokens = re.findall(r"[0-9A-Za-z]{2,}", text)
        n = len(tokens)
        for size in range(1, 8):
            for i in range(n - size + 1):
                candidate = "".join(tokens[i:i+size]).upper()
                if GSTIN_STRICT.search(candidate):
                    found.append(GSTIN_STRICT.search(candidate).group())
                    if len(found) >= 2:
                        return found
    return found

def normalize_label(s: str) -> str:
    s = (s or "").upper().strip()
    s = s.replace(" ", "").replace(":", "")
    s = s.replace("C6ST", "CGST").replace("CG5T", "CGST").replace("COST", "CGST")
    s = s.replace("S6ST", "SGST").replace("SG5T", "SGST")
    s = s.replace("1GST", "IGST").replace("I6ST", "IGST").replace("IG5T", "IGST")
    return s

def collapse_spaced_numbers(line: str) -> str:
    s = line
    s = re.sub(r'(?<=\d)\s+(?=[\d\.,])', '', s)
    s = re.sub(r'(?<=[\d\.,])\s+(?=\d)', '', s)
    s = re.sub(r'(?<=\d)\s+(?=\d)', '', s)
    s = re.sub(r'\s{2,}', ' ', s)
    return s

def normalize_ocr_line(line: str) -> str:
    if not line:
        return ""
    ln = line.strip()
    ln = ln.replace('\t', ' ')
    ln = collapse_spaced_numbers(ln)
    ln = ln.replace("TAXA8LE", "TAXABLE").replace("TAXABIE", "TAXABLE")
    ln = ln.replace("TAXA BLE", "TAXABLE")
    ln = re.sub(r'\bC\s*G\s*S\s*T\b', 'CGST', ln, flags=re.I)
    ln = re.sub(r'\bS\s*G\s*S\s*T\b', 'SGST', ln, flags=re.I)
    ln = re.sub(r'\bI\s*G\s*S\s*T\b', 'IGST', ln, flags=re.I)
    ln = normalize_label(ln)
    return ln

# ---------------- PDF & OCR functions ---------------
def read_text_layer(pdf_bytes: io.BytesIO) -> str:
    text = ""
    try:
        reader = PdfReader(pdf_bytes)
        for p in reader.pages:
            t = p.extract_text()
            if t:
                text += t + "\n"
    except Exception:
        return ""
    return text

def pdf_page_to_image(pdf_bytes: io.BytesIO, page_no: int = 0, dpi: int = 300) -> Image.Image:
    pdf_bytes.seek(0)
    pdf = fitz.open(stream=pdf_bytes.read(), filetype="pdf")
    page = pdf[page_no]
    pix = page.get_pixmap(dpi=dpi)
    mode = "RGBA" if pix.alpha else "RGB"
    img = Image.frombytes(mode, (pix.width, pix.height), pix.samples)
    if pix.alpha:
        img = img.convert("RGB")
    pdf.close()
    return img

def preprocess_for_high_accuracy(pil_img: Image.Image) -> Image.Image:
    try:
        img = pil_img.convert("RGB")
        if OPENCV_AVAILABLE:
            arr = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)
            gray = cv2.cvtColor(arr, cv2.COLOR_BGR2GRAY)
            gray = cv2.GaussianBlur(gray, (3,3), 0)
            _, th = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            coords = np.column_stack(np.where(th < 255))
            if coords.shape[0] > 0:
                rect = cv2.minAreaRect(coords)
                angle = rect[-1]
                if angle < -45:
                    angle = -(90 + angle)
                else:
                    angle = -angle
                if abs(angle) > 0.1:
                    (h, w) = th.shape[:2]
                    M = cv2.getRotationMatrix2D((w//2, h//2), angle, 1.0)
                    th = cv2.warpAffine(th, M, (w, h), flags=cv2.INTER_CUBIC, borderMode=cv2.BORDER_REPLICATE)
            return Image.fromarray(th).convert("RGB")
        else:
            img = ImageOps.grayscale(img)
            img = img.filter(ImageFilter.MedianFilter(size=3))
            img = img.point(lambda p: 255 if p > 180 else 0)
            return img.convert("RGB")
    except Exception:
        return pil_img

def ocr_lines_from_image(pil_img: Image.Image, config: str = TESS_CONFIG_TEXT) -> List[str]:
    raw = pytesseract.image_to_string(pil_img, config=config, lang='eng')
    lines = raw.splitlines()
    cleaned = []
    for ln in lines:
        ln2 = normalize_ocr_line(ln)
        if ln2.strip():
            cleaned.append(ln2)
    return cleaned

def ocr_words_with_positions(pil_img: Image.Image, config: str = TESS_CONFIG_TEXT) -> List[Tuple[str,int,int,int,int]]:
    data = pytesseract.image_to_data(pil_img, output_type=Output.DICT, config=config, lang='eng')
    out = []
    n = len(data['text'])
    for i in range(n):
        txt = data['text'][i]
        if not txt or str(txt).strip() == "":
            continue
        out.append((normalize_ocr_line(txt), int(data['left'][i]), int(data['top'][i]), int(data['width'][i]), int(data['height'][i])))
    return out

# ---------------- GST extraction ----------------
def extract_gst_values_from_lines(lines: List[str]) -> dict:
    res = {"Taxable_Value": 0.0, "CGST": 0.0, "SGST": 0.0, "IGST": 0.0}
    for ln in lines:
        up = ln.upper()
        if "TAXABLE" in up and re.search(r'[\d]', ln):
            m = re.search(r'([\d]{1,3}(?:[,\d]*\d)?(?:\.\d+)?)$', ln.replace(' ', ''))
            if not m:
                m = re.search(r'([\d,]+\.\d+|[\d,]+)', ln)
            if m:
                res["Taxable_Value"] = max(res["Taxable_Value"], safe_float(m.group(1)))
                continue
        if "CGST" in up or "CENTRAL" in up:
            m = re.search(r'([\d,]+\.\d+|[\d,]+)$', ln)
            if not m:
                m = re.search(r'([\d,]+\.\d+|[\d,]+)', ln)
            if m:
                res["CGST"] = max(res["CGST"], safe_float(m.group(1)))
                continue
        if "SGST" in up or "STATE" in up:
            m = re.search(r'([\d,]+\.\d+|[\d,]+)$', ln)
            if not m:
                m = re.search(r'([\d,]+\.\d+|[\d,]+)', ln)
            if m:
                res["SGST"] = max(res["SGST"], safe_float(m.group(1)))
                continue
        if "IGST" in up or "INTEGRATED" in up:
            m = re.search(r'([\d,]+\.\d+|[\d,]+)$', ln)
            if not m:
                m = re.search(r'([\d,]+\.\d+|[\d,]+)', ln)
            if m:
                res["IGST"] = max(res["IGST"], safe_float(m.group(1)))
                continue
    if res["Taxable_Value"] == 0.0:
        nums = []
        for ln in lines[-10:]:
            for n in re.findall(r'[\d,]+\.\d+|[\d,]+', ln):
                nums.append(safe_float(n))
        if nums:
            nums_sorted = sorted(set(nums))
            if len(nums_sorted) >= 2:
                res["Taxable_Value"] = nums_sorted[-2]
            else:
                res["Taxable_Value"] = nums_sorted[-1]
    return res

def extract_gstins_from_lines(lines: List[str]) -> Tuple[str,str,str,str]:
    joined = "\n".join(lines)
    found = find_gstins_in_text(joined)
    seller = found[0] if len(found) > 0 else ""
    buyer = found[1] if len(found) > 1 else ""
    return seller, extract_state_code_from_gstin(seller), buyer, extract_state_code_from_gstin(buyer)

# ---------------- IMPROVED INVOICE NUMBER EXTRACTION ----------------
# ---------------- IMPROVED INVOICE NUMBER EXTRACTION ----------------
# ---------------- IMPROVED INVOICE NUMBER EXTRACTION ----------------
def extract_invoice_number_from_lines(lines: List[str]) -> str:
    joined = "\n".join(lines)
    
    def clean_invoice(s: str) -> str:
        s = s.strip()
        # Extract the part that matches invoice pattern (like 1/25-26/863)
        m = re.search(r'(\d{1,4}/\d{2}-\d{2}/\d{1,6})', s)
        return m.group(1) if m else s

    label_keywords = re.compile(r'\b(INVOICE|INV|BILL|TAX INVOICE)\b', re.IGNORECASE)
    for i, ln in enumerate(lines):
        if label_keywords.search(ln):
            # Check current line first
            inv = clean_invoice(ln)
            if inv:
                return inv
            # Then check next line if needed
            if i + 1 < len(lines):
                inv = clean_invoice(lines[i+1])
                if inv:
                    return inv

    # Fallback: search entire text
    inv = clean_invoice(joined)
    if inv:
        return inv

    return ""




# ---------------- The rest of the code (AI, extraction, DB, Google Drive, Scheduler) ----------------
# You keep the rest of your code unchanged, just replace the previous extract_invoice_number_from_lines with the one above.


# ---------------- AI (Azure) optional --------------
def ai_extract(text: str) -> dict:
    """Optional: Azure OpenAI extraction. Non-blocking fallback to OCR exists."""
    if not (AZURE_OPENAI_KEY and AZURE_OPENAI_ENDPOINT and AZURE_DEPLOYMENT):
        return {}
    try:
        import openai
        openai.api_type = "azure"
        openai.api_key = AZURE_OPENAI_KEY
        openai.api_base = AZURE_OPENAI_ENDPOINT.rstrip("/")
        openai.api_version = "2024-02-01"
        prompt = f"""
Extract invoice into JSON. Return missing numeric fields as 0.
Fields:
Date, Total_Amount, Invoice_Number, IRN,
Seller_Name, Seller_GSTIN_UIN, Seller_State_Name_Code,
Buyer_Name, Buyer_GSTIN_UIN, Buyer_State_Name_Code,
Buyer_Order_No, Destination, HSN_SAC,
IGST, CGST, SGST, Taxable_Value, Total_Tax_Amount

Text:
{text}
"""
        # Try a couple of interfaces to be compatible with different openai client versions
        try:
            resp = openai.ChatCompletion.create(
                engine=AZURE_DEPLOYMENT,
                messages=[{"role":"system","content":"Return ONLY JSON"},{"role":"user","content":prompt}],
                temperature=0
            )
            content = ""
            if isinstance(resp, dict):
                content = resp["choices"][0]["message"]["content"]
            else:
                content = getattr(resp.choices[0].message, "content", "") or str(resp)
            m = re.search(r"\{.*\}", content, re.S)
            return json.loads(m.group()) if m else {}
        except Exception:
            try:
                resp = openai.chat.completions.create(
                    model=AZURE_DEPLOYMENT,
                    messages=[{"role":"system","content":"Return ONLY JSON"},{"role":"user","content":prompt}],
                    temperature=0
                )
                content = resp.choices[0].message.content
                m = re.search(r"\{.*\}", content, re.S)
                return json.loads(m.group()) if m else {}
            except Exception:
                return {}
    except Exception:
        return {}

# -------------- High-level field extraction combining everything -------------
def extract_fields_from_pdfbytes(pdf_bytes: io.BytesIO) -> dict:
    """
    Steps:
      1. Try text layer (fast)
      2. Run high-accuracy OCR pass (DPI high, preprocessing) -> extract lines
      3. Run fallback OCR pass (lower DPI)
      4. Merge results: prefer text-layer values if present and non-zero; otherwise OCR
    """
    pdf_bytes.seek(0)
    result = {}
    # 1. text-layer extraction
    text_layer = read_text_layer(pdf_bytes)
    text_lines = []
    if text_layer and text_layer.strip():
        text_lines = [normalize_ocr_line(l) for l in text_layer.splitlines() if l.strip()]
    # collect all candidate lines
    all_lines = list(text_lines)  # prefer text layer first

    # 2. High-accuracy OCR (first try)
    try:
        img = pdf_page_to_image(pdf_bytes, page_no=0, dpi=HIGH_ACCURACY_DPI)
        proc = preprocess_for_high_accuracy(img)
        ha_lines = ocr_lines_from_image(proc, config=TESS_CONFIG_TEXT)
        if DEBUG_OCR:
            print("HIGH-ACCURACY OCR LINES:\n", ha_lines[:40])
        # append lines that are new
        for l in ha_lines:
            if l not in all_lines:
                all_lines.append(l)
    except Exception as e:
        if DEBUG_OCR:
            print("High accuracy OCR failed:", e)

    # 3. Fallback OCR (quicker)
    try:
        img2 = pdf_page_to_image(pdf_bytes, page_no=0, dpi=FALLBACK_DPI)
        proc2 = preprocess_for_high_accuracy(img2) if not OPENCV_AVAILABLE else img2
        fb_lines = ocr_lines_from_image(proc2, config=TESS_CONFIG_TEXT)
        if DEBUG_OCR:
            print("FALLBACK OCR LINES:\n", fb_lines[:40])
        for l in fb_lines:
            if l not in all_lines:
                all_lines.append(l)
    except Exception:
        pass

    # If still empty, fallback to words with positions (we can reconstruct rows)
    if not all_lines:
        try:
            img3 = pdf_page_to_image(pdf_bytes, page_no=0, dpi=FALLBACK_DPI)
            words = ocr_words_with_positions(img3, config=TESS_CONFIG_TEXT)
            # simple line reconstruction by grouping by 'top' coordinate
            lines_map = {}
            for w, left, top, width, height in words:
                key = top // 10  # bucket
                lines_map.setdefault(key, []).append((left, w))
            reconstructed = []
            for k in sorted(lines_map.keys()):
                parts = sorted(lines_map[k], key=lambda x: x[0])
                line = " ".join([p[1] for p in parts])
                reconstructed.append(normalize_ocr_line(line))
            for l in reconstructed:
                if l not in all_lines:
                    all_lines.append(l)
        except Exception:
            pass

    # Merge and dedupe preserve order
    merged_lines = []
    seen = set()
    for l in all_lines:
        lf = l.strip()
        if lf and lf not in seen:
            merged_lines.append(lf)
            seen.add(lf)

    if DEBUG_OCR:
        print("--- MERGED LINES ---")
        for ln in merged_lines[:80]:
            print(ln)
    # 4. Extract GST numeric values and GSTINs
    gst_values = extract_gst_values_from_lines(merged_lines)
    seller_gstin, seller_state, buyer_gstin, buyer_state = extract_gstins_from_lines(merged_lines)

    # 5. AI extraction for textual fields if azure present (optional)
    ai = {}
    try:
        joined_text = "\n".join(merged_lines)
        ai = ai_extract(joined_text) or {}
    except Exception:
        ai = {}

    # Merge: prefer ai/text-layer for textual fields, prefer numeric from OCR if ai missing
    fields = {}
    # textual fields set (attempt to fill from ai first)
    textual_keys = ["Date","Total_Amount","Invoice_Number","IRN","Seller_Name",
                    "Seller_GSTIN_UIN","Seller_State_Name_Code","Buyer_Name",
                    "Buyer_GSTIN_UIN","Buyer_State_Name_Code","Buyer_Order_No",
                    "Destination","HSN_SAC"]
    for k in textual_keys:
        val = ai.get(k, "") or ""
        fields[k] = val

    # numeric: use ai if present and >0 else use gst_values
    fields["Taxable_Value"] = round(safe_float(ai.get("Taxable_Value", gst_values.get("Taxable_Value", 0))), 2)
    fields["CGST"] = round(safe_float(ai.get("CGST", gst_values.get("CGST", 0))), 2)
    fields["SGST"] = round(safe_float(ai.get("SGST", gst_values.get("SGST", 0))), 2)
    fields["IGST"] = round(safe_float(ai.get("IGST", gst_values.get("IGST", 0))), 2)

    # Try to extract Total_Amount from lines if ai empty
    if not fields.get("Total_Amount"):
        # look for "TOTAL" or last large number
        total_candidate = 0.0
        for ln in reversed(merged_lines[-15:]):
            if re.search(r'\bTOTAL\b', ln.upper()) and re.search(r'[\d]', ln):
                m = re.search(r'([\d,]+\.\d+|[\d,]+)', ln)
                if m:
                    total_candidate = safe_float(m.group(1))
                    break
        if total_candidate == 0.0:
            # fallback = max numeric
            nums = []
            for ln in merged_lines[-30:]:
                nums += [safe_float(n) for n in re.findall(r'[\d,]+\.\d+|[\d,]+', ln)]
            nums = [n for n in nums if n and n>0]
            if nums:
                total_candidate = max(nums)
        fields["Total_Amount"] = round(total_candidate, 2)

    # If IGST missing but total-taxable > 0 and AUTO_INFER flag: infer IGST
    if AUTO_INFER_IGST_IF_MISSING and fields["IGST"] == 0 and fields["Total_Amount"] and fields["Taxable_Value"]:
        inferred = round(fields["Total_Amount"] - fields["Taxable_Value"], 2)
        if inferred > 0:
            # only set if CGST+SGST are zero (i.e., interstate case)
            if fields["CGST"] == 0 and fields["SGST"] == 0:
                fields["IGST"] = inferred

    # Total_Tax_Amount
    fields["Total_Tax_Amount"] = round(fields["IGST"] + fields["CGST"] + fields["SGST"], 2)

    # GSTINs and states
    if not fields.get("Seller_GSTIN_UIN"):
        fields["Seller_GSTIN_UIN"] = seller_gstin
    if not fields.get("Seller_State_Name_Code"):
        fields["Seller_State_Name_Code"] = seller_state
    if not fields.get("Buyer_GSTIN_UIN"):
        fields["Buyer_GSTIN_UIN"] = buyer_gstin
    if not fields.get("Buyer_State_Name_Code"):
        fields["Buyer_State_Name_Code"] = buyer_state

    # NEW: improved invoice number extraction when AI/text-layer missing or noisy
    if not fields.get("Invoice_Number"):
        inv = extract_invoice_number_from_lines(merged_lines)
        if inv:
            fields["Invoice_Number"] = inv

    # fill empty textual fields with empty string
    for k in textual_keys:
        if k not in fields:
            fields[k] = ""

    return fields

# ---------------- Drive helpers ----------------
def list_pdfs(folder_id: str):
    q = f"'{folder_id}' in parents and mimeType='application/pdf' and trashed=false"
    res = drive_service.files().list(q=q, fields="files(id,name)").execute()
    return res.get("files", [])

def download_pdf(file_id: str) -> io.BytesIO:
    req = drive_service.files().get_media(fileId=file_id)
    fh = io.BytesIO()
    downloader = MediaIoBaseDownload(fh, req)
    done = False
    while not done:
        _, done = downloader.next_chunk()
    fh.seek(0)
    return fh

def move_to_processed(file_id: str, processed_folder_id: str):
    """
    Move a PDF file to the 'Processed' folder on Google Drive.
    Ensures it doesn't get added twice and logs all actions.
    """
    try:
        # Get current parent folders
        file = drive_service.files().get(fileId=file_id, fields="parents, name").execute()
        current_parents = file.get("parents", [])
        file_name = file.get("name", "Unknown")

        if not current_parents:
            print(f"[WARN] File {file_name} has no parent folder.")
        
        # If already in processed folder, skip
        if processed_folder_id in current_parents:
            print(f"[INFO] File '{file_name}' is already in the processed folder. Skipping move.")
            return

        # Remove current parents and add processed folder
        drive_service.files().update(
            fileId=file_id,
            addParents=processed_folder_id,
            removeParents=",".join(current_parents),
            fields="id, parents"
        ).execute()
        print(f"[SUCCESS] Moved '{file_name}' to processed folder.")

    except Exception as e:
        print(f"[ERROR] Failed to move file '{file_id}' to processed folder: {e}")



# --------------- Save functions ----------------
def save_to_db(row: dict):
    row["Upload_Date"] = datetime.now().strftime("%Y-%m-%d")
    row["Upload_Time"] = datetime.now().strftime("%H:%M:%S")
    values = [row.get(c, "") for c in COLUMNS]
    placeholders = ",".join(["?"]*len(values))
    try:
        cur.execute(f"INSERT INTO invoices ({','.join(COLUMNS)}) VALUES ({placeholders})", values)
        conn.commit()
    except Exception as e:
        print("DB save failed:", e)
        conn.rollback()

def save_to_sheet(row: dict):
    """
    Safely append invoice row to Google Sheet.
    Ensures header exists and data aligns properly.
    Retries 3 times on failure.
    """
    MAX_RETRIES = 3
    RETRY_DELAY = 2  # seconds

    for attempt in range(1, MAX_RETRIES + 1):
        try:
            sh = sheet_client.open_by_key(SHEET_ID).sheet1

            # Ensure header exists
            existing = sh.get_all_values()
            if not existing or existing[0] != COLUMNS:
                sh.clear()
                time.sleep(1)
                sh.append_row(COLUMNS)
                time.sleep(1)

            # Ensure row matches number of columns
            values = [row.get(c, "") for c in COLUMNS]
            if len(values) < len(COLUMNS):
                values += [""] * (len(COLUMNS) - len(values))
            elif len(values) > len(COLUMNS):
                values = values[:len(COLUMNS)]

            sh.append_row(values)
            print(f"Google Sheet append successful for invoice: {row.get('Invoice_Number','')}")
            return  # success

        except Exception as e:
            print(f"Google Sheet append attempt {attempt} failed:", e)
            if attempt < MAX_RETRIES:
                time.sleep(RETRY_DELAY)
            else:
                print(f"Google Sheet append permanently failed for invoice: {row.get('Invoice_Number','')}")




# ---------------- Main processing ----------------
STOP_FLAG = False
STOP_LOCK = threading.Lock()

def process_all():
    global STOP_FLAG
    pdfs = list_pdfs(INPUT_FOLDER_ID)
    if not pdfs:
        print("No invoices found.")
        return
    for f in pdfs:
        with STOP_LOCK:
            if STOP_FLAG:
                print("Stop flag set — aborting batch.")
                return
        fid = f["id"]
        name = f["name"]
        print(f"\nProcessing: {name}")
        try:
            pdf_bytes = download_pdf(fid)
        except Exception as e:
            print("Download failed:", e)
            continue
        try:
            fields = extract_fields_from_pdfbytes(pdf_bytes)
            fields["Source_File"] = name
            # pretty print
            print(tabulate([[fields.get(c, "") for c in COLUMNS]], headers=COLUMNS, tablefmt="grid"))
            save_to_db(fields)
            save_to_sheet(fields)
            move_to_processed(fid, PROCESSED_FOLDER_ID)

        except Exception as e:
            print("Processing failed:", e)
            import traceback; traceback.print_exc()
        with STOP_LOCK:
            if STOP_FLAG:
                print("Stop flag detected — finishing.")
                return
    print("\nBatch complete.\n")

# --------------- Scheduler & input watcher ----------------
def scheduled_job():
    with STOP_LOCK:
        if STOP_FLAG:
            return
    print("\n[Auto Scheduler] Running automatic invoice processing...\n")
    process_all()

def schedule_thread():
    # schedule already set by start()
    while True:
        with STOP_LOCK:
            if STOP_FLAG:
                break
        schedule.run_pending()
        time.sleep(1)

def input_watcher():
    """Waits for 'q' on stdin; immediate stop."""
    global STOP_FLAG
    try:
        while True:
            line = sys.stdin.readline()
            if not line:
                time.sleep(0.2)
                continue
            if line.strip().lower() == "q":
                print("\n'q' received — shutting down.")
                with STOP_LOCK:
                    STOP_FLAG = True
                break
    except Exception as e:
        print("input_watcher error:", e)
        with STOP_LOCK:
            STOP_FLAG = True

def start():
    global STOP_FLAG
    print("\n========== Invoice Automation Started ==========")
    print("→ Auto-runs every 12 hours (first run now).")
    print("→ Type 'q' + ENTER anytime to stop immediately.")
    print("================================================\n")

    schedule.clear()
    schedule.every(12).hours.do(scheduled_job)
    # run first immediately
    scheduled_job()

    t_sched = threading.Thread(target=schedule_thread, daemon=True)
    t_sched.start()
    t_input = threading.Thread(target=input_watcher, daemon=True)
    t_input.start()

    try:
        while True:
            with STOP_LOCK:
                if STOP_FLAG:
                    break
            time.sleep(0.5)
    except KeyboardInterrupt:
        print("KeyboardInterrupt — stopping.")
        with STOP_LOCK:
            STOP_FLAG = True

    # give threads a moment to finish
    time.sleep(1)
    try:
        conn.close()
    except:
        pass
    print("System stopped. Exiting.")
    sys.exit(0)

if __name__ == "__main__":
    start()
