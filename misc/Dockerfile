# If you modify this file, make sure to update the BUILD_IMAGE variable in .gitlab-ci.yml.

FROM debian:buster-slim

USER root

# install dependencies
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -yq && \
    apt-get upgrade -yq --with-new-pkgs --auto-remove && \
    apt-get install -yq --no-install-recommends autoconf build-essential ca-certificates git g++ libboost-dev libmpfr-dev ocaml-nox unzip wget && \
    apt-get clean

RUN wget --quiet https://github.com/ocaml/opam/releases/download/2.0.6/opam-2.0.6-x86_64-linux -O /usr/local/bin/opam && \
    chmod a+x /usr/local/bin/opam

# create user
RUN adduser --disabled-password --gecos '' user
USER user
ENV HOME /home/user
WORKDIR /home/user

# install gappa
RUN wget --quiet https://gforge.inria.fr/frs/download.php/file/38044/gappa-1.3.5.tar.gz && \
  tar xzf gappa-1.3.5.tar.gz && \
  cd gappa-1.3.5 && \
  ./configure && \
  ./remake && \
  cd .. && \
  mkdir -p .local/bin && \
  cp gappa-1.3.5/src/gappa .local/bin/ && \
  rm -rf gappa-1.3.5 gappa-1.3.5.tar.gz

# install opam
ENV OPAM_PACKAGES="conf-autoconf conf-g++"
RUN opam init -y --no-setup -j1 --bare --disable-sandboxing && \
    opam switch create minimal ocaml-system && opam install -y $OPAM_PACKAGES && \
    opam switch create latest  ocaml-system && opam install -y $OPAM_PACKAGES && \
    opam install -y --switch=minimal coq.8.8.2 && \
    opam install -y --switch=latest  coq.8.11.0 && \
    opam repository add coq-released https://coq.inria.fr/opam/released --all-switches && \
    opam install -y --switch=minimal coq-flocq.3.0.0 && \
    opam install -y --switch=latest  coq-flocq.3.2.1 && \
    opam clean -a -c -r -s --logs
