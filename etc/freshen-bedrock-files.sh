#!/usr/bin/env bash

MYDIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$MYDIR" 1>/dev/null

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

FILES="$(git grep --name-only "Bedrock\.")"

COQLIB="$(${COQBIN}coqc -config | grep 'COQLIB=' | sed s'/^COQLIB=//g')"

MYCOQPATH="$COQPATH${COQPATH:+:}$COQLIB"

echo "My COQPATH is $MYCOQPATH"

for VFILE in $FILES; do
  if [ ! -e "$VFILE" ]; then
    echo "Could not find $VFILE"
    continue
  elif [ ! -e "${VFILE}o" ]; then
    echo "Already going to rebuild ${VFILE}o"
    continue
  fi

  VOFILES="$(grep -o "Bedrock\.[^ ]*" "$VFILE" | sed s'/\.$//g' | sed s'|\.|/|g' | sed s'/$/.vo/g' | sort | uniq)"
  for VOFILE in $VOFILES; do
    if [ ! -e "${VFILE}o" ]; then # we already got rid of it
      break
    fi
    FOUND=""
  ( IFS=:
    for DIR in $MYCOQPATH; do
      if [ -e "$DIR/$VOFILE" ]; then
        FOUND=1
        if [ "$DIR/$VOFILE" -nt "${VFILE}o" ]; then
          echo "Now going to rebuild ${VFILE}o; $DIR/$VOFILE is newer"
          rm -f "${VFILE}o"
        else
          echo "Not necessarily rebuilding ${VFILE}o; $DIR/$VOFILE is older"
        fi
        break
      fi
    done
    if [ -z "$FOUND" ]; then
      echo "WARNING: Could not find $VOFILE, which $VFILE depends on"
    fi
   )
  done
done

popd 1>/dev/null
