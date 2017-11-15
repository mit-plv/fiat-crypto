/* WARNING: This file was copied from Specific/CurveParameters/montgomery64/fesquare.c.
 If you edit it here, changes will be erased the next time remake_curves.sh is run. */
static void fesquare(uint64_t *out, const uint64_t *in) {
  femul(out, in, in);
}
