pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv DList.
from Jasmin require import JModel.

require import Params Types BaseW Address Hash.

(******************************************************************************)

(* type key = nbytes. *)
(* type seed = nbytes. *)

(* (******************************************************************************) *)

(* type wots_message = nbytes. *)
(* type wots_message_base_w = onebyte. *)
(* type wots_signature = len_nbytes. *)
(* type wots_pk = len_nbytes. *)
(* type wots_sk = len_nbytes. *)
(* type wots_keypair = wots_pk * wots_sk. *)

(* (******************************************************************************) *)

(* subtype wots_ots_keys as OTSKeys = { l : wots_sk list | size l = 2^h }. *)
(* realize inhabited. *)
(* proof. *)
(* by exists (nseq (2^h) witness); rewrite size_nseq; smt(ge0_h @IntDiv). *)
(* qed. *)

op nbytexor(a b : nbytes) : nbytes = NBytes.insubd (bytexor (NBytes.val a) (NBytes.val b)).

module Chain = {
   proc chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes = {
      (*
       *
       * i: start index
       * s: number of steps
       *
       *)
    var t : nbytes <- X;
    var chain_count : int <- 0;
    var _key : key;
    var bitmask : nbytes;
    var addr_bytes : nbytes;

    (* case i + s <= w-1 is precondition *)
    while (chain_count < s) {
     address <- set_hash_addr address (i + chain_count);
     address <- set_key_and_mask address 0;

      addr_bytes <- addr_to_bytes address;
     _key <@ Hash.prf(addr_bytes, _seed);

     address <- set_key_and_mask address 1;

     addr_bytes <- addr_to_bytes address;
     bitmask <@ Hash.prf(addr_bytes, _seed);

     t <@ Hash._F (_key, (nbytexor t bitmask));

     chain_count <- chain_count + 1;
    }

    return t;
   }
}.

pred chain_pre(X : nbytes, i s : int, _seed : seed, address : adrs) = 
    0 <= s <= w-1.

op chain_body (i : int) (_s : seed) (chain_count : int) (ta : nbytes * adrs) =
  let (t, ad) = ta in
  let ad = set_hash_addr ad (i + chain_count) in
  let ad = set_key_and_mask ad 0 in
  let addr_bytes = addr_to_bytes ad in
  let _key = prf addr_bytes _s in
  let ad = set_key_and_mask ad 1 in
  let addr_bytes = addr_to_bytes ad in
  let bitmask = prf addr_bytes _s in
  (_F _key (nbytexor t bitmask), ad).

op chain (x : nbytes) (i s : int) (_s : seed) (ad : adrs): nbytes =
  fst (iteri s (chain_body i _s) (x, ad)).

hoare chain_eq _X _i _s _se _ad:
  Chain.chain: arg = (_X, _i, _s, _se, _ad) ==> res = chain _X _i _s _se _ad.
proof.
proc.
case (s < 0).
+ rcondf ^while; auto => /> ?; 1: smt().
  by rewrite /chain iteri0 /#.
while (i = _i
    /\ _seed = _se
    /\ s = _s
    /\ (t, address) = iteri chain_count (chain_body _i _se) (_X, _ad)
    /\ 0 <= chain_count <= s).
+ wp; ecall (_F_eq _key (nbytexor t bitmask))=> //=.
  wp; ecall (prf_eq addr_bytes _seed)=> //=.
  wp; ecall (prf_eq addr_bytes _seed)=> //=.
  auto=> /> &0 ih ge0_cc _ cc_lt_s.
  by rewrite iteriS // -ih /chain_body //= /#.
by auto=> />; rewrite iteri0 //= /#.
qed.

op f (_s : seed) (ad : adrs) (x : nbytes): nbytes =
  let ad = set_key_and_mask ad 0 in
  let addr_bytes = addr_to_bytes ad in
  let _key = prf addr_bytes _s in
  let ad = set_key_and_mask ad 1 in
  let addr_bytes = addr_to_bytes ad in
  let bitmask = prf addr_bytes _s in
  _F _key (nbytexor x bitmask).

op ch (f : seed -> adrs -> nbytes -> nbytes) (_s : seed) (ad : adrs) (i s : int) (x : nbytes): nbytes =
  iteri s (fun chain_count x => f _s (set_hash_addr ad (i + chain_count)) x) x.

lemma ch0 (g : seed -> adrs -> nbytes -> nbytes) (ps : seed) (ad : adrs) (s i : int) (x : nbytes) :
     i <= 0
  => ch g ps ad s i x = x.
proof. by move=> ge0 @/ch; rewrite iteri0. qed.

lemma chS (g : seed -> adrs -> nbytes -> nbytes) (ps : seed) (ad : adrs) (s i : int) (x : nbytes) :
     0 < i
  => ch g ps ad s i x = g ps (set_hash_addr ad (s + i - 1)) (ch g ps ad s (i - 1) x).
proof. by move=> ge0_s @/ch; rewrite (iteriS (i - 1)) /#. qed.

lemma chain_body_eq_ad (i : int) (_s : seed) (chain_count : int) (ta : nbytes * adrs):
  forall j,
       0 <= j < 8
    => j <> 6
    => j <> 7
    => Array8.Array8."_.[_]" (chain_body i _s chain_count ta).`2 j = Array8.Array8."_.[_]" ta.`2 j.
proof.
case: ta=> t a /= j j_rng j_neq_6 j_neq_7 @/chain_body //=.
by rewrite !Array8.Array8.set_neqiE.
qed.

lemma chain_eq_ad (x : nbytes) (i s : int) (_s : seed) (ad : adrs):
  forall j,
       0 <= j < 8
    => j <> 6
    => j <> 7
    => Array8.Array8."_.[_]" (iteri s (chain_body i _s) (x, ad)).`2 j = Array8.Array8."_.[_]" ad j.
proof.
move=> j j_rng j_neq7 j_neq6.
case: (0 <= s); last first.
+ by move=> lt0_s; rewrite iteri0 /#.
elim: s=> [|s ge0_s ih].
+ by rewrite iteri0 //.
by rewrite iteriS 1:// chain_body_eq_ad.
qed.

lemma chain_eq_ch_f _X _i _s _se _ad:
  chain _X _i _s _se _ad = ch f _se _ad _i _s _X.
proof.
case: (0 <= _s); last first.
+ by move=> /ltzNge le0_s @/chain; rewrite iteri0 2:ch0 /#.
elim: _s=> [|_s ge0_s ih].
+ by rewrite /chain iteri0 2:ch0.
rewrite chS 1://#.
have ->: _i + (_s + 1) - 1 = _i + _s.
+ smt().
have ->: _s + 1 - 1 = _s by done.
rewrite -ih.
rewrite /chain iteriS // {1}/chain_body /f //=.
case _: (iteri _s (chain_body _i _se) (_X, _ad))=> t ad /= tadP.
have -> //: set_key_and_mask (set_hash_addr  ad (_i + _s)) 0
          = set_key_and_mask (set_hash_addr _ad (_i + _s)) 0.
apply: Array8.Array8.ext_eq=> j j_rng.
case: (j = 7)=> [->> //|j_neq7].
case: (j = 6)=> [->> //|j_neq6].
rewrite !Array8.Array8.set_neqiE //.
have ->: ad = (iteri _s (chain_body _i _se) (_X, _ad)).`2 by rewrite tadP.
by rewrite chain_eq_ad.
qed.

module WOTS = {
  (* In practise, we generate the private key from a secret seed *)
  proc genSK() : wots_sk = {
    var sk : W8.t list list;
    var sk_i : W8.t list;
    var i : int;

    sk <-(nseq len (nseq n W8.zero));
    i <- 0;

    while (i < len) {
      sk_i <$ DList.dlist W8.dword n; (* Initialize sk[i] with a uniformly random n-byte string *)
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return LenNBytes.insubd (map NBytes.insubd sk);
  }

  (*
  Pseudorandom Key Generation [Section 3.1.7. of the RFC]

    During key generation, a uniformly random n-byte string S is
    sampled from a secure source of randomness. This string S is stored
    as private key. The private key elements are computed as sk[i] =
    PRF(S, toByte(i, 32)) whenever needed. Please note that this seed S
    MUST be different from the seed SEED used to randomize the hash
    function calls. Also, this seed S MUST be kept secret. The seed S
    MUST NOT be a low entropy, human-memorable value since private key
    elements are derived from S deterministically and their
    confidentiality is security-critical.

  *)
  proc pseudorandom_genSK(sk_seed : nbytes, seed : nbytes, address : adrs) : wots_sk = {
    var sk : nbytes list;
    var sk_i : nbytes;
    var addr_bytes : nbytes;
    var buf : W8.t list;
    var i : int;

    sk <-  nseq len witness;

    address <- set_hash_addr address 0;
    address <- set_key_and_mask address 0;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      addr_bytes <- addr_to_bytes address;
      sk_i <@ Hash.prf_keygen (NBytes.val seed ++ NBytes.val addr_bytes, sk_seed);
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return LenNBytes.insubd sk;
  }

  (* The len n-byte strings in the private key each define the start node for one hash chain. The public
  key consists of the end nodes of these hash chains *)
  proc genPK(sk : wots_sk, _seed : seed, address : adrs) : wots_pk = {
    var pk : nbytes list;
    var i : int;
    var pk_i, sk_i : nbytes;

    pk <- nseq len witness;
    i <- 0;

    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness (LenNBytes.val sk) i;
      pk_i <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return LenNBytes.insubd pk;
  }

  (* Generates the key from the seed *)
  proc pkGen(sk_seed : nbytes, _seed : seed, address : adrs) : wots_pk  = {
    var pk : nbytes list;
    var wots_skey : wots_sk;
    var i : int;
    var pk_i, sk_i : nbytes;

    pk <- nseq len witness;
    i <- 0;


    wots_skey <@ pseudorandom_genSK(sk_seed, _seed, address); (* Generate sk from the secret key *)
    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness (LenNBytes.val wots_skey) i;
      pk_i <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return LenNBytes.insubd pk;
  }

  proc kg(sk_seed : nbytes, _seed : seed, address : adrs) : wots_keypair = {
    var pk : wots_pk;
    var sk : wots_sk;

    sk <@ pseudorandom_genSK(sk_seed, _seed, address);
    pk <@ genPK(sk, _seed, address);

    return (pk, sk);
  }

  proc checksum (m : int list) : int = {
    var i : int <- 0;
    var m_i : int;
    var checksum : int;

    checksum <- 0;

    while (i < len1) {
      m_i <- nth witness m i;
      checksum <- checksum + (w - 1) - m_i;
      i <- i + 1;
    }

    return checksum;
  }

  (*
               +---------------------------------+
               |                                 |
               |           sig_ots[0]            |    n bytes
               |                                 |
               +---------------------------------+
               |                                 |
               ~              ....               ~
               |                                 |
               +---------------------------------+
               |                                 |
               |          sig_ots[len - 1]       |    n bytes
               |                                 |
               +---------------------------------+

                                WOTS+ Signature
  *)

  proc sign(M : wots_message, sk : wots_sk, _seed : seed, address : adrs) : wots_signature = {
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var msg_i : int;
    var sk_i : nbytes;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var sig : nbytes list;
    var sig_i : nbytes;
    var i : int;

    sig <- nseq len witness;

    (* Convert message to base w *)
    msg <@ BaseW.base_w(NBytes.val M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int ( 8 - ( ( len2 * log2_w) ) %% 8 );
    len_2_bytes <- ceil( ( len2 * log2_w )%r / 8%r );

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len2;
    csum_base_w <@ BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sk_i <- nth witness (LenNBytes.val sk) i;
      sig_i <@ Chain.chain (sk_i, 0, msg_i, _seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return LenNBytes.insubd sig;
  }

  proc sign_seed (M : W8.t list, sk_seed : seed, pub_seed : seed, address : adrs) : wots_signature = {
    var wots_skey : wots_sk;
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var msg_i : int;
    var sk_i : nbytes;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var sig : nbytes list;
    var sig_i : nbytes;
    var i : int;

    sig <- nseq len witness;

    (* Generate sk from the secret seed *)
    wots_skey <@ pseudorandom_genSK(sk_seed, pub_seed, address); 

    (* Convert message to base w *)
    msg <@ BaseW.base_w(M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    (*
    RFC:
          csum = csum << ( 8 - ( ( len_2 * lg(w) ) % 8 ));
          len_2_bytes = ceil( ( len_2 * lg(w) ) / 8 );

     *)
    csum_32 <- csum_32 `<<` W8.of_int ( 8 - ( ( len2 * log2_w ) %% 8 ));
    len_2_bytes <- ceil ( (len2 * log2_w)%r / 8%r );

    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sk_i <- nth witness (LenNBytes.val wots_skey) i;
      sig_i <@ Chain.chain (sk_i, 0, msg_i, pub_seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return LenNBytes.insubd sig;
  }

  proc pkFromSig(M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : wots_pk = {
    var tmp_pk : nbytes list;
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var i : int;
    var sig_i : nbytes;
    var msg_i : int;
    var pk_i : nbytes;

    tmp_pk <-  nseq len witness;
    (* Convert message to base w *)
    msg <@ BaseW.base_w(NBytes.val M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - (len2 * log2_w) %% 8);
    len_2_bytes <- ceil ( (len2 * log2_w)%r / 8%r);

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sig_i <- nth witness (LenNBytes.val sig) i;
      pk_i <@ Chain.chain (sig_i, msg_i, (w - 1 - msg_i), _seed, address);
      tmp_pk <- put tmp_pk i pk_i;
      i <- i + 1;
    }

    return LenNBytes.insubd tmp_pk;
  }

  proc verify(pk : wots_pk, M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : bool = {
    var tmp_pk : wots_pk;
    tmp_pk <@ pkFromSig(M, sig, _seed, address);
    return pk = tmp_pk;
  }
}.

