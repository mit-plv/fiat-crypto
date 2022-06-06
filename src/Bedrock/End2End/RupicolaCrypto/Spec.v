Require Coq.Init.Byte Coq.Strings.String. Export Init.Byte(byte(..)) String.
Require Export coqutil.Datatypes.List. Export Lists.List List.ListNotations.
Require Export Coq.ZArith.BinInt. Export Zdiv. Local Open Scope Z_scope.
Require Export coqutil.Byte coqutil.Word.LittleEndianList.


Require Import Crypto.Arithmetic.PrimeFieldTheorems.

(* reference: https://datatracker.ietf.org/doc/html/rfc8439 *)

(*
In terms of Z:
Definition poly1305 (p:=2^130-5) (k : list byte) (m : list byte) : list byte :=
  let r := Z.land (le_combine (firstn 16 k)) 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let t := fold_left (fun a n => (a+le_combine(n++[x01]))*r mod p) (chunk 16 m) 0 in
  le_split 16 (t + le_combine (skipn 16 k)).

TODO: prove equivalent to current spec
*)

Definition poly1305 (p:=(2^130-5)%positive) (k : list byte) (m : list byte) : list byte :=
  let r := F.of_Z p (Z.land (le_combine (firstn 16 k)) 0x0ffffffc0ffffffc0ffffffc0fffffff) in
  let t := fold_left (fun a n => (a+(F.of_Z p (le_combine(n++[x01]))))*r)%F (chunk 16 m) 0%F in
  le_split 16 ((F.to_Z t) + le_combine (skipn 16 k)).

Local Notation "a + b" := (Z.land (a+b) (Z.ones 32)).
Local Notation "a ^ b" := (Z.lxor a b).
Local Notation "a <<< b" := (Z.shiftl a b + Z.shiftr a (32-b))
  (at level 30).

Definition quarter '(a, b, c, d) :=
  let a := a + b in  let d := d ^ a in  let d := d <<< 16 in
  let c := c + d in  let b := b ^ c in  let b := b <<< 12 in
  let a := a + b in  let d := d ^ a in  let d := d <<< 8 in
  let c := c + d in  let b := b ^ c in  let b := b <<< 7 in
  (a, b, c, d).

Definition quarterround x y z t (st : list Z) :=
  let '(a,b,c,d) := quarter (nth x st 0, nth y st 0, nth z st 0, nth t st 0) in
  upd (upd (upd (upd st x a) y b) z c) t d.

Definition chacha20_block (*256bit*)key (*32bit+96bit*)nonce :=
  let st := (*512bit*)
    map le_combine (chunk 4 (list_byte_of_string"expand 32-byte k"))
    ++ map le_combine (chunk 4 key)
    ++ map le_combine (chunk 4 nonce) in
  let ss := Nat.iter 10 (fun ss =>
    let ss := quarterround  0  4  8 12  ss in
    let ss := quarterround  1  5  9 13  ss in
    let ss := quarterround  2  6 10 14  ss in
    let ss := quarterround  3  7 11 15  ss in
    let ss := quarterround  0  5 10 15  ss in
    let ss := quarterround  1  6 11 12  ss in
    let ss := quarterround  2  7  8 13  ss in
    let ss := quarterround  3  4  9 14  ss in
    ss) st in
  let st := map (fun '(s, t) => s + t) (combine ss st) in
  flat_map (le_split 4) st.

Definition chacha20_encrypt key start nonce plaintext :=
  flat_map (fun '(counter, ck) =>
    zip byte.xor (chacha20_block key (le_split 4 (Z.of_nat counter) ++ nonce)) ck)
  (enumerate start (chunk 64 plaintext)).

Definition chacha20poly1305_aead_encrypt aad key iv constant plaintext :=
  let pad16 xs := repeat x00 (Nat.div_up (length xs) 16 * 16 - length xs) in
  let nonce := constant ++ iv in
  let otk := firstn 32 (chacha20_block key (le_split 4 0 ++ nonce)) in
  let ciphertext := chacha20_encrypt key 1 nonce plaintext in
  let mac_data := aad ++ pad16 aad in
  let mac_data := mac_data ++ ciphertext ++ pad16 ciphertext in
  let mac_data := mac_data ++ le_split 8 (Z.of_nat (length aad)) in
  let mac_data := mac_data ++ le_split 8 (Z.of_nat (length ciphertext)) in
  let tag := poly1305 otk mac_data in
  (ciphertext, tag).
