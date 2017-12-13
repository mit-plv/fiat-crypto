#!/usr/bin/env bash

cd "$( dirname "${BASH_SOURCE[0]}" )"
cd ../..
sed s'|^src/Specific/montgomery.*||g' -i _CoqProject
sed s'|^src/Specific/solinas.*||g' -i _CoqProject
