FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update
RUN apt-get install -y gcc make git
RUN apt-get install -y curl m4 ruby

# OCaml
WORKDIR /root
RUN curl -L https://github.com/ocaml/ocaml/archive/4.02.1.tar.gz |tar -xz
WORKDIR ocaml-4.02.1
RUN ./configure
RUN make world.opt
RUN make install

# OPAM
WORKDIR /root
RUN curl -L https://github.com/ocaml/opam/archive/1.2.0.tar.gz |tar -xz
WORKDIR opam-1.2.0
RUN ./configure
RUN make lib-ext
RUN make
RUN make install

# Initialize OPAM
RUN opam init
ENV OPAMJOBS 4

# Coq
RUN opam install -y coq

# YoJson and SmartPrint
RUN opam install -y yojson smart-print

# CoqOfOCaml
ADD . /root/coq-of-ocaml
WORKDIR /root/coq-of-ocaml
# Coq code
WORKDIR OCaml
RUN eval `opam config env`; ./configure.sh && make && make install
# OCaml code
WORKDIR ..
RUN eval `opam config env`; make
