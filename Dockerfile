FROM python:3.11-slim

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    LTL_HOST=0.0.0.0 \
    LTL_PORT=8080 \
    LTL_DATA_DIR=/data

WORKDIR /srv

COPY app ./app
COPY tests ./tests
COPY scripts ./scripts

# 零第三方运行时依赖；构建期语法检查，失败即中断构建
RUN python -m py_compile app/*.py

RUN mkdir -p /data
VOLUME ["/data"]

EXPOSE 8080

HEALTHCHECK --interval=10s --timeout=3s --start-period=5s --retries=5 \
    CMD ["python", "/srv/app/healthcheck.py"]

CMD ["python", "-m", "app.server"]
