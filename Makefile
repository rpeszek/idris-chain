
DEFAULT: build

clean:
	idris --clean idris-chain.ipkg

all: install

install: build
	idris --install idris-chain.ipkg

build: 
	idris --build idris-chain.ipkg
