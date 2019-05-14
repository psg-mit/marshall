FROM ubuntu:18.04

# install dependencies

RUN apt-get update && \
    apt-get upgrade -y 

# install opam
RUN apt-get install -y software-properties-common
RUN add-apt-repository ppa:avsm/ppa  
RUN apt-get update
RUN apt-get install -y ocaml ocaml-native-compilers camlp4-extra opam=2.0.4-0ppa1\~bionic

# install make
RUN apt-get install -y build-essential

# install remaining dependencies
RUN apt-get install -y \
        m4=1.4.18-1 \
	rlwrap=0.43-1 \
	libmpfr-dev=4.0.1-1

# add the repo to the container
RUN mkdir /shapes
COPY . /shapes

# initialize opam dependencies
RUN opam init -y --disable-sandboxing
RUN opam switch create 4.04.0
RUN cd shapes && opam install -y . 
 
RUN echo "Hello world"
#CMD
