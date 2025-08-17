"""
Simple FastAPI demo showing buggy vs. fixed file upload approaches.

This is a minimal example that implements the behaviors modeled in the TLA+ specs:
- /upload_buggy: Uses random UUIDs (non-idempotent, creates duplicates)
- /upload_hashed: Uses content hashing (idempotent, safe retries)

Demonstrates how formal verification with TLA+ translates to real implementations.
"""
import os, uuid, hashlib, boto3
from fastapi import FastAPI, UploadFile, File, HTTPException

MINIO_ENDPOINT = os.environ["MINIO_ENDPOINT"]
MINIO_ACCESS_KEY = os.environ["MINIO_ACCESS_KEY"]
MINIO_SECRET_KEY = os.environ["MINIO_SECRET_KEY"]
BUCKET = os.environ.get("BUCKET", "assets")

s3 = boto3.client(
    "s3",
    endpoint_url=MINIO_ENDPOINT,
    aws_access_key_id=MINIO_ACCESS_KEY,
    aws_secret_access_key=MINIO_SECRET_KEY,
)

app = FastAPI(title="FastAPI + MinIO tiny demo")

def ensure_bucket():
    try:
        s3.head_bucket(Bucket=BUCKET)
    except Exception:
        s3.create_bucket(Bucket=BUCKET)

@app.on_event("startup")
def on_startup():
    ensure_bucket()

@app.get("/")
def root():
    return {"ok": True, "endpoints": ["/upload_buggy", "/upload_hashed"]}

# ❌ BUGGY: random filenames ⇒ duplicates on retries
@app.post("/upload_buggy")
async def upload_buggy(file: UploadFile = File(...)):
    data = await file.read()
    if not data:
        raise HTTPException(400, "Empty file")
    key = f"uploads/{uuid.uuid4().hex}.bin"  # non-idempotent
    s3.put_object(Bucket=BUCKET, Key=key, Body=data)
    return {"bucket": BUCKET, "key": key, "size": len(data), "note": "non-idempotent filename"}

# ✅ FIXED: content-addressed key (idempotent)
@app.post("/upload_hashed")
async def upload_hashed(file: UploadFile = File(...)):
    data = await file.read()
    if not data:
        raise HTTPException(400, "Empty file")
    h = hashlib.sha256(data).hexdigest()
    key = f"uploads/{h}"
    # Put is safe to repeat; same key overwrites the same logical object
    s3.put_object(Bucket=BUCKET, Key=key, Body=data,
                  Metadata={"sha256": h})
    return {"bucket": BUCKET, "key": key, "sha256": h, "size": len(data), "note": "idempotent filename"}
