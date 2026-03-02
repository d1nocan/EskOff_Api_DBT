FROM python:3.11-slim
WORKDIR /app
COPY build_all.py .
CMD ["python3", "build_all.py", "--only", "db", "--upload", "--serve"]
