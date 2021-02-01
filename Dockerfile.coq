FROM ubuntu:18.04 

RUN apt update -y 
RUN apt install -y \
    coq \
    git \
    screen \
    software-properties-common 

RUN add-apt-repository ppa:kelleyk/emacs -y

RUN apt install -y emacs27


RUN git clone https://github.com/leechanwoo/emacs_for_coq.git ~/emacs_for_coq
RUN cp ~/emacs_for_coq/.emacs ~/

WORKDIR /home

