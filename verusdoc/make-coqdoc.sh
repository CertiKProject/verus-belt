#!/bin/bash

coqdoc --light --html ../src/guarding/guard.v --utf8
coqdoc --light --html ../src/guarding/guard_later_pers.v --utf8
coqdoc --light --html ../src/guarding/factoring_props.v --utf8

coqdoc --light --html ../src/guarding/lib/rwlock.v --utf8
coqdoc --light --html ../src/guarding/lib/non_atomic_map.v --utf8
coqdoc --light --html ../src/guarding/lib/lifetime.v --utf8
coqdoc --light --html ../src/guarding/lib/lifetime_full.v --utf8
coqdoc --light --html ../src/guarding/lib/boxes.v --utf8
