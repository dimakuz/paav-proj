NAME=project
IN_TEX=${NAME}.tex
OUT_PDF=${NAME}.pdf

CFGS=${PARITY_CFGS} ${SUM_CFGS} ${SHAPE_CFGS}
PARITY_CFGS=$(patsubst %, ${CURDIR}/parity/examples/example%-output/cfg.png,1 2 3 4 5)
# SUM_CFGS=$(patsubst %, ${CURDIR}/sum/examples/example%-output/cfg.png,1 2 3 4 5)

all: ${OUT_PDF}

%.pdf: %.tex $(shell find ${NAME} -type f -name '*.tex') cfgs
	xelatex $<

%-output/cfg.png: %.code
	(cd ..;  pipenv run analyze --no-debug --type $(shell basename $(shell dirname $(shell dirname $<))) --output $(dir $@) $<)

clean:
	rm -f ${NAME}.log ${NAME}.aux ${NAME}.out ${NAME}.pdf
	rm -rf parity/examples/example*-output/
	rm -rf sum/examples/example*-output/
	rm -rf shape/examples/example*-output/

cfgs: ${CFGS}

.PHONY: clean all cfgs
