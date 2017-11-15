/* WARNING: This file was copied from Specific/CurveParameters/montgomery32/fesquare.c.
 If you edit it here, changes will be erased the next time remake_curves.sh is run. */
static void fesquare(uint32_t *out, const uint32_t *in) {
  femul(out, in, in);
}
