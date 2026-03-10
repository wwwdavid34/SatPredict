FROM python:3.11-slim

WORKDIR /app

# Install Python dependencies
COPY pyproject.toml .
COPY src/ src/
RUN pip install --no-cache-dir ".[web]" numpy requests sgp4 jdcal

# Copy application code
COPY SatPredict.py .
COPY app_local/ app_local/
COPY scripts/ scripts/

# Create data directory for SQLite DB
RUN mkdir -p data

# Expose port (Railway sets PORT env var)
EXPOSE 8000

CMD ["sh", "-c", "uvicorn app_local.api.main:app --host 0.0.0.0 --port ${PORT:-8000}"]
