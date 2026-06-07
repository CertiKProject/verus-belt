#!/bin/bash

coqdoc --light --html ../src/guarding/guard.v --utf8
coqdoc --light --html ../src/guarding/guard_later_pers.v --utf8
coqdoc --light --html ../src/guarding/factoring_props.v --utf8

coqdoc --light --html ../src/lambda_verus/lifetime/lifetime_full.v --utf8
coqdoc --light --html ../src/lambda_verus/util/non_atomic_cell_map.v --utf8
coqdoc --light --html ../src/lambda_verus/lang/lifting.v --utf8
