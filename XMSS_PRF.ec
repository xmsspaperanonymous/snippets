pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import XMSS_Params Types Address BaseW Hash WOTS LTree XMSS_TreeHash.
import Params OTSKeys ThreeNBytesBytes AuthPath.
import Array8.


module XMSS_PRF = {
    proc sample_randomness () : nbytes * nbytes * nbytes = {
    var sk_seed, sk_prf, pub_seed : W8.t list;

    sk_seed  <$ DList.dlist W8.dword n;
    sk_prf   <$ DList.dlist W8.dword n;
    pub_seed <$ DList.dlist W8.dword n;

    return (NBytes.insubd sk_seed, NBytes.insubd sk_prf, NBytes.insubd pub_seed);
  }

   proc kg() : xmss_keypair = {
      var pk : xmss_pk <- witness;
      var sk : xmss_sk <- witness;

      var sk_seed, sk_prf, pub_seed, root : nbytes;

      var address : adrs <- zero_address;
      address <- set_layer_addr address 0;
      
      (sk_seed, sk_prf, pub_seed) <@ sample_randomness();

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=witness;
             |};

      root <@ TreeHash.treehash(pub_seed, sk_seed, 0, h, address);

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=root;
             |};

      pk <- {| pk_oid=impl_oid; pk_root=root; pk_pub_seed=pub_seed |};

      return (sk, pk);
   }

proc sign(sk : xmss_sk, m : msg_t) : sig_t * xmss_sk = {
    var idx : W32.t;
    var idx_new : W32.t;
    var address : adrs;
    var _R : nbytes;
    var _M' : nbytes;
    var ots_sig : wots_signature;
    var auth : auth_path;
    var sig : sig_t;
    var idx_bytes : nbytes;
    var idx_nbytes : nbytes;
    var root : nbytes;
    var t : threen_bytes;
    var sk_prf : nbytes <- sk.`sk_prf;
    
    idx <- sk.`idx;
    idx_new <- sk.`idx + W32.one;
    sk <- {| sk with idx=idx_new |};
    address <- zero_address;
    
    idx_bytes <- NBytes.insubd (toByte idx n);

    _R <@ Hash.prf(idx_bytes, sk_prf);

    root <- sk.`sk_root;
    t <- ThreeNBytesBytes.insubd (NBytes.val _R ++ NBytes.val root ++ NBytes.val idx_bytes);
    _M' <- H_msg t m;

    (ots_sig, auth) <@ TreeSig.treesig(_M', sk, idx, address);

    sig <- {| sig_idx = idx; r = _R ; r_sig = (ots_sig, auth) |}; 
  
    return (sig, sk);
  }

 proc verify(pk : xmss_pk, m : msg_t, s : sig_t) : bool = {
    var is_valid : bool;
    var idx_sig : W32.t;
    var idx_bytes : nbytes;
    var node, root, _R, _M': nbytes;    
    var auth : auth_path;
    var sig_ots : wots_signature;
    var _seed : seed;
    var address : adrs;
    var t : threen_bytes;

    idx_sig <- s.`sig_idx;
    idx_bytes <- NBytes.insubd (toByte idx_sig n);
    _seed <- pk.`pk_pub_seed;
    address <- zero_address;
    (sig_ots,auth) <- s.`r_sig; 

    root <- pk.`pk_root;
    _R <- s.`r;
    t <- ThreeNBytesBytes.insubd (NBytes.val _R ++ NBytes.val root ++ NBytes.val idx_bytes);
    _M' <- H_msg t m;
    
    node <@ RootFromSig.rootFromSig(idx_sig, sig_ots, auth, _M', _seed, address);

    is_valid <- (node = root);

    return is_valid;
  }  
}.
