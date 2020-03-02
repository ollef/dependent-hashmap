# dependent-hashmap [![Build Status](https://travis-ci.com/ollef/dependent-hashmap.svg?branch=master)](https://travis-ci.com/ollef/dependent-hashmap) [![Hackage](https://img.shields.io/hackage/v/dependent-hashmap.svg)](https://hackage.haskell.org/package/dependent-hashmap)

This is hash map library where the keys can specify the type of value that is associated with them by using type indices.

This library is to
[dependent-map](https://github.com/mokus0/dependent-map) what `Data.HashMap.Lazy` is to `Data.Map`.

It's implemented as a thin wrapper around `Data.HashMap.Lazy`, and
has roughly the same interface.
