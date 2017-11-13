#/bin/bash
( 
  for f in $(find . -name gmpxx.log); do echo -e "$(basename "$(dirname "$f")" | cut -d_ -f2-)\tgmpxx\t$(cat "$f" | cut -d' ' -f3 | cut -d, -f1)"; done
  for f in $(find . -name gmpsec.log); do echo -e "$(basename "$(dirname "$f")" | cut -d_ -f2-)\tgmpsec\t$(cat "$f" | cut -d' ' -f3 | cut -d, -f1)"; done
  for f in $(find . -name gmpvar.log); do echo -e "$(basename "$(dirname "$f")" | cut -d_ -f2-)\tgmpvar\t$(cat "$f" | cut -d' ' -f3 | cut -d, -f1)"; done
  for f in $(find . -name fibe.log); do echo -e "$(basename "$(dirname "$f")" | cut -d_ -f2-)\tfibe_$(basename "$(dirname "$f")" | cut -d_ -f1)\t$(cat "$f" | cut -d' ' -f3 | cut -d, -f1)"; done
) \
| sort -n -k3 | sed 's:fibe:fiat:g' | sed 's/\(\d\)m\(\d\)/\1-\2/g' | sed 's/\(\d\)e\(\d\)/\1^\2/g'  | sed 's/\(\d\)x\(\d\)/\1*\2/g'  | sed 's/\(\d\)p\(\d\)/\1+\2/g' 
