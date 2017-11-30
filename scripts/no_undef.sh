#!/usr/bin/env bash
perl -p -i \
	-e 's/nsw/ /g; s/nuw/ /g; s/exact/ /g; s/inbounds/ /g' \
	"${1}"
