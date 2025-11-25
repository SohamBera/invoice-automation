# app.py
from flask import Flask, request, render_template, redirect, url_for, flash
import io
import threading
import os
from chat import process_all, STOP_LOCK, STOP_FLAG, start  # import functions from chat.py

app = Flask(__name__)
app.secret_key = os.getenv("FLASK_SECRET_KEY", "supersecretkey")

# Home page: upload or trigger processing
@app.route("/", methods=["GET", "POST"])
def index():
    if request.method == "POST":
        action = request.form.get("action")
        if action == "process_drive":
            threading.Thread(target=process_all, daemon=True).start()
            flash("Started processing invoices from Google Drive...", "info")
        elif action == "stop":
            global STOP_FLAG
            with STOP_LOCK:
                STOP_FLAG = True
            flash("Processing will stop shortly.", "warning")
        return redirect(url_for("index"))
    return render_template("index.html")

# Optional route to upload PDF directly
@app.route("/upload", methods=["POST"])
def upload_pdf():
    if "file" not in request.files:
        flash("No file uploaded", "danger")
        return redirect(url_for("index"))
    file = request.files["file"]
    if file.filename == "":
        flash("No selected file", "danger")
        return redirect(url_for("index"))
    pdf_bytes = io.BytesIO(file.read())
    threading.Thread(target=process_uploaded_pdf, args=(pdf_bytes,file.filename), daemon=True).start()
    flash(f"Processing {file.filename} in background...", "success")
    return redirect(url_for("index"))

def process_uploaded_pdf(pdf_bytes, filename):
    from chat import extract_fields_from_pdfbytes, save_to_db, save_to_sheet
    try:
        fields = extract_fields_from_pdfbytes(pdf_bytes)
        fields["Source_File"] = filename
        save_to_db(fields)
        save_to_sheet(fields)
        print(f"Processed uploaded PDF: {filename}")
    except Exception as e:
        print("Failed to process uploaded PDF:", e)

if __name__ == "__main__":
    # Optionally start the auto-scheduler from chat.py
    threading.Thread(target=start, daemon=True).start()
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", 5000)), debug=True)
