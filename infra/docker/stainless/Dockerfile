# Use an official OpenJDK runtime as a parent image
FROM ubuntu:22.04

# Install dependencies for Stainless
RUN apt-get update && apt-get install -y \
    wget \
    curl \
    git \
    zip \
    unzip \
    build-essential \
    gnupg \
    ca-certificates \
    z3

# Install SBT (Scala Build Tool)
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian all main" | tee /etc/apt/sources.list.d/sbt.list
RUN curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x99E82A75642AC823" | apt-key add
RUN apt-get update && apt-get install -y sbt scala

RUN curl -s https://repos.azul.com/azul-repo.key | gpg --dearmor -o /usr/share/keyrings/azul.gpg
RUN echo "deb [signed-by=/usr/share/keyrings/azul.gpg] https://repos.azul.com/zulu/deb stable main" | tee /etc/apt/sources.list.d/zulu.list
RUN apt update
RUN apt install zulu21-jdk -y
RUN java --version

# Set working directory
RUN mkdir /opt/stainless
WORKDIR /opt/stainless

# Install Stainless
RUN wget https://github.com/epfl-lara/stainless/releases/download/v0.9.8.8/stainless-dotty-standalone-0.9.8.8-linux.zip
RUN unzip *.zip

# Set Stainless to the PATH
ENV PATH="/opt/stainless:${PATH}"

# Verify installation
RUN stainless --help

RUN mkdir -p /app
WORKDIR /app
# Command to run Stainless verification (which will be set by docker-compose)
# CMD ["stainless"]
