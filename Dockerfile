FROM ubuntu:bionic

# Root commands
RUN apt-get update && apt-get install -y python3 python3-virtualenv sudo git binutils g++ gcc make libdpkg-perl python-dev libpython3.6-dev coreutils wget && \
    rm -rf /var/lib/apt/lists/* && \
    useradd -m pySym && \
    echo 'pySym ALL=(ALL) NOPASSWD:ALL' | sudo EDITOR='tee -a' visudo

WORKDIR /home/pySym

USER pySym

COPY . /home/pySym/pySym/

ARG Z3URL=https://github.com/Z3Prover/z3/archive/Z3-4.8.5.tar.gz

RUN mkdir /home/pySym/.virtualenvs && \
    sudo chown -R pySym:pySym /home/pySym/. && \
    python3 -m virtualenv --python=$(which python3) ~/.virtualenvs/pySym && \
    echo ". ~/.virtualenvs/pySym/bin/activate" >> ~/.bashrc && \
    . ~/.virtualenvs/pySym/bin/activate && cd pySym && PYSYM_NO_Z3=True pip install -e .[dev] && \
    cd lib/z3 && wget -O z3.tar.gz $Z3URL && tar xf z3.tar.gz && mv */* . && python scripts/mk_make.py --python && \
    cd build && make -j$(nproc) && make install

CMD ["/bin/bash","-i"]
