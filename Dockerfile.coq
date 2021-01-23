FROM ubuntu:18.04 

RUN apt update -y 
RUN apt install -y \
    coq \
    emacs \
    git \
    screen 

RUN git clone https://github.com/leechanwoo/emacs_for_coq.git ~/emacs_for_coq
RUN cp ~/emacs_for_coq/.emacs ~/

WORKDIR /home

