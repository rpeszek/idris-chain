module Blockchain

import Data.Hash

%default total
-- TODO public export is temporary
%access public export

{- 
   Conceptual, dependently typed implementation of a blockchain using 
   (not cryptographic) Data.Hash.
   I plan on trying to covert this to use
     https://github.com/idris-hackers/idris-crypto

   This module implements blockchain (cryptographic linked list) that provides
   type level guarantee of cryptographic correctness of hashes.
   It does not implement anything else (P2P networking, payloads stored in chain, 
   consensus protocol, etc).
-}

------------------------------
--- HList and other utilitities
------------------------------
namespace HList
  infixr 7 ::
  data HList : List Type -> Type where
    HNil : HList []
    (::) : t -> HList ts -> HList (t :: ts)

  ||| Show instance is used for testing
  Show (HList []) where 
     show x = "HNil"
  (Show a, Show (HList xs)) => Show (HList (a :: xs)) where
     show (t :: xt) = (show t) ++ "::" ++ (show xt)
  
||| Testing convenience class
||| ```idris example
|||  the (List String) (asList ("2" :: 1 :: HNil))
||| ```
||| Interstingly doing something similar with Monoids 
||| does not seem to go far  
interface AsList a b where 
   asList : a -> List b
AsList (HList []) b where
   asList = const []
(AsList (HList xs) b, Cast a b) => AsList (HList (a :: xs)) b where 
   asList (t :: xt) = (cast t) :: (asList xt)
||| Idris does not have this 
||| https://github.com/idris-lang/Idris-dev/issues/3479
Cast a a where
   cast = id

-----------------------------------------------
-- Temporary non-crypto hashing abstracted out
-----------------------------------------------

BlockHash : Type
BlockHash = Bits64

GenesisHash : BlockHash
GenesisHash = hash () 

GenesisFn : () -> BlockHash 
GenesisFn = hash -- (const (hash ())) 

strHash : String -> BlockHash
strHash = hash

--------------------
-- DSLs
--------------------

||| Conceptual code does not want to concern itself with particulars
||| of how this is done. The implementation of this interface is assumed 
||| to correctly compute hashes. 
||| TODO think about it more - move to a more explicit hashing?
interface BlockData a where
    serialize : a -> String
    blockHash : a -> BlockHash 
    blockHash = strHash . serialize
    prevHash : a -> BlockHash

-- Interestingly things stop compiling if blockHash method is moved out from
-- the interface!
-- blockHash : BlockData a => a -> BlockHash 
-- blockHash = strHash . serialize

--------------------------------
-- Simple homogenious blockchain 
--------------------------------

namespace SimpleBlockchain
  ||| See Test.Blockchain for example
  data SimpleBlockchain : (payload : Type) -> (hash : BlockHash) -> Type where 
     Genesis : SimpleBlockchain a GenesisHash
     (::) : BlockData a => (payload : a) -> SimpleBlockchain a (prevHash payload) -> SimpleBlockchain a (blockHash payload) 

--------------------------------------------------
-- Heterogenous blockchain with varying payloads 
-- Can blockchain be general purpose and store various types of payloads?
-------------------------------------------------- 

-- TODO this is getting better but still needs more thinking

namespace Block
  ||| `Block payload hash hash_fn` looks like standard dependently typed 
  |||  indexed monad (or state machine).
  |||  @ payload that contains previous hash and can be hashed (satisfies BlockData contraint) 
  |||  @ hash links previous block
  |||  @ hash_fn hash function that knows how to sign the payload
  data Block : (payload : Type) -> (hash: BlockHash) -> (hash_fn : payload -> BlockHash) -> Type where
      MkBlock : BlockData a => (payload : a) -> Block a (prevHash payload) blockHash
      
      Genesis : Block () 0 GenesisFn 
      ||| This is currently not used, 
      ||| monadic function verifies (on type level) previous payload hash (payload : a) and 
      ||| exposes proof of that verification (hash2_fn payload) 
      ||| as well as provides hash function that works on its own payload.
      (>>=) : Block a hash1 hash2_fn ->
              ((payload : a) -> Block b (hash2_fn payload) hash3_fn) ->
              Block b (hash2_fn payload) hash3_fn

extractPayload : Block a h hash_fn -> a
extractPayload (MkBlock p) = p
extractPayload Genesis = ()
extractPayload (block1 >>= fn) = extractPayload (fn (extractPayload block1))

extractPrevHash : Block a h hash_fn -> BlockHash
extractPrevHash (MkBlock p) = prevHash p
extractPrevHash Genesis = 0
extractPrevHash (block1 >>= fn) = extractPrevHash (fn (extractPayload block1))

computeHash : Block a h hash_fn -> BlockHash
computeHash (MkBlock p) = blockHash p
computeHash Genesis = GenesisFn ()
computeHash (block1 >>= fn) = computeHash (fn (extractPayload block1))

namespace HBlockchain
  ||| This blockchain allows heterogeneous blocks with different payloads and different
  ||| (payload dependent) hashing algorithms.  
  ||| The crypto-correctness of the chain is guaranteed by the type.
  |||
  ||| This blockchain maintains the 'running' last block hash
  ||| @ payloads the type level list of payload types does not buy me much except for 
  ||| having a simple extractPayloads function
  data HBlockchain : (payloads : List Type) -> BlockHash -> Type where
       Single : Block () 0 GenesisFn -> HBlockchain [] GenesisHash
       (::) : (block : Block a h1 hash_fn) -> HBlockchain ax h1 -> HBlockchain (a::ax) (hash_fn (extractPayload block))

extractPayloads : HBlockchain payloads hs -> HList payloads 
extractPayloads (Single g) = HNil
extractPayloads (block :: chain) =  (extractPayload block) :: extractPayloads chain

||| Untyping convenient for testing
AsList (HList payloads) b => AsList (HBlockchain payloads hs) b where 
   asList = asList . extractPayloads

extractPrevHashes : HBlockchain payloads hs -> List BlockHash 
extractPrevHashes (Single g) = [0]
extractPrevHashes (block :: chain) = (extractPrevHash block) :: extractPrevHashes chain

computeHashes : HBlockchain payloads hs -> List BlockHash 
computeHashes (Single g) = [GenesisFn ()]
computeHashes (block :: chain) = (computeHash block) :: computeHashes chain

-------------------------------
-- Examples
-- for example usage see `Test.Blockchain` module
-------------------------------
exampleMiner : BlockData a => (payload : a) -> HBlockchain ax (prevHash payload) -> HBlockchain (a :: ax) (blockHash payload)
exampleMiner payload chain =  (MkBlock payload) :: chain 
