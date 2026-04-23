#!/bin/sh

START_DIR="$(pwd)"

cd ~/.cabal/store || exit 1
zip -r cabal-store.zip ghc-9.4.7/ || exit 1

cp cabal-store.zip "$START_DIR"/ || exit 1
