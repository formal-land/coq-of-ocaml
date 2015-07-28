FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update
RUN apt-get install -y gcc make git
RUN apt-get install -y curl m4 ruby
RUN apt-get install -y unzip

# OCaml
WORKDIR /root
RUN curl -L https://github.com/ocaml/ocaml/archive/4.02.2.tar.gz |tar -xz
WORKDIR ocaml-4.02.2
RUN ./configure && make world.opt && make install

# OPAM
WORKDIR /root
RUN curl -L https://github.com/ocaml/opam/archive/1.2.2.tar.gz |tar -xz
WORKDIR opam-1.2.2
RUN ./configure && make lib-ext && make && make install

# Initialize OPAM
RUN opam init
ENV OPAMJOBS 2

# Coq
RUN opam install -y coq

# YoJson and SmartPrint
RUN opam install -y yojson smart-print

# CoqOfOCaml
ADD . /root/coq-of-ocaml
WORKDIR /root/coq-of-ocaml
# Coq code
WORKDIR CoqOfOCaml
RUN eval `opam config env`; ./configure.sh && make && make install
# OCaml code
WORKDIR ..
RUN eval `opam config env`; make
