#!/usr/bin/bash
cat $1 | addr2line -apfCse target/x86_64-epiphyllum/debug/epiphyllum