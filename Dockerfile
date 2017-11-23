FROM ubuntu:17.10

# Root commands
RUN apt-get update && apt-get install -y python3 python3-virtualenv sudo git binutils g++ gcc make libdpkg-perl python-dev libpython3.6-dev && \
    rm -rf /var/lib/apt/lists/* && \
    useradd -m pySym && \
    echo 'pySym ALL=(ALL) NOPASSWD:ALL' | sudo EDITOR='tee -a' visudo

WORKDIR /home/pySym

USER pySym

COPY . /home/pySym/pySym/

RUN mkdir /home/pySym/.virtualenvs && \
    sudo chown -R pySym:pySym /home/pySym/. && \
    python3 -m virtualenv --python=$(which python3) ~/.virtualenvs/pySym && \
    echo ". ~/.virtualenvs/pySym/bin/activate" >> ~/.bashrc && \
    . ~/.virtualenvs/pySym/bin/activate && cd pySym && pip install -e .[dev]

CMD ["/bin/bash","-i"]
