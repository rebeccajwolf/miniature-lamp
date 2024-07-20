FROM alpine:3.16

# Set default environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ="America/New_York"
ENV PYTHONUNBUFFERED=1

# Create working directory and relevant dirs
WORKDIR /app
RUN chmod 777 /app

RUN apk update && apk add --no-cache bash \
  curl \
  wget \
  git \
  unzip \
  coreutils \
  gtk+2.0 \
  gdk-pixbuf \
  python3-dev \
  py3-pip \
  python3-tkinter \
  tzdata \
  xvfb \
  zlib-dev \
  build-base \
  linux-headers \
  chromium \
  chromium-chromedriver

RUN cp /usr/share/zoneinfo/$TZ /etc/localtime

ENV PATH="$PATH:/.local/"

RUN pip install -U pip


# Add often-changed files in order to cache above
COPY . .

RUN pip install --no-cache-dir -r requirements.txt

# Make the entrypoint executable
RUN chmod +x entrypoint.sh

# Set the entrypoint to our entrypoint.sh

ENTRYPOINT ["/app/entrypoint.sh"]

#END