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

   This module implements Blockchain (cryptographic linked list) that provides
   type level guarantee of cryptographic correctness of hashes.
   It does not implement anything else (P2P networking, payloads stored in chain, 
   consensus protocol, etc).
-}

------------------------------
--- HList needed as a utilitity
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

--------------------
-- DSLs
--------------------

BlockHash : Type
BlockHash = Bits64

GenesisHash : Bits64
GenesisHash = hash () 

GenesisFn : () -> BlockHash 
GenesisFn = hash -- (const (hash ())) 

strHash : String -> BlockHash
strHash = hash

||| Conceptual code does not want to concern itself with particulars
||| of how this is done. The implementation of this interface is assumed 
||| to correctly compute hashes. 
||| TODO think about it more - move to a more explicit hashing?
interface BlockData a where
    serialize : a -> String
    blockHash : a -> BlockHash 
    blockHash = strHash . serialize
    prevHash : a -> BlockHash

-- Interestingly things stop compiling if blockHash method is moved out!
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
  ||| `Block payload hash hash_fn` looks like standard dependently typed indexed monad.
  |||  @ payload that contains previous hash and can be hashed (satisfies BlockData contraint) 
  |||  @ hash links previous block
  |||  @ hash_fn hash function that knows how to sign the payload
  data Block : (payload : Type) -> (hash: BlockHash) -> (hash_fn : payload -> BlockHash) -> Type where
      MkBlock : BlockData a => (payload : a) -> Block a (prevHash payload) blockHash
      
      Genesis : Block () 0 GenesisFn 
      ||| This is currently not used, 
      ||| monadic function verifies previous payload (payload : a) and exposes proof of that verification
      ||| (hash2_fn payload) as well as provides hash function that works on its own payload.
      (>>=) : Block a hash1 hash2_fn ->
              ((payload : a) -> Block b (hash2_fn payload) hash3_fn) ->
              Block b (hash2_fn payload) hash3_fn

getPayload : Block a h hash_fn -> a
getPayload (MkBlock p) = p
getPayload Genesis = ()
getPayload (block1 >>= fn) = getPayload (fn (getPayload block1))

extractPrevHash : Block a h hash_fn -> BlockHash
extractPrevHash (MkBlock p) = prevHash p
extractPrevHash Genesis = 0
extractPrevHash (block1 >>= fn) = extractPrevHash (fn (getPayload block1))

computeHash : Block a h hash_fn -> BlockHash
computeHash (MkBlock p) = blockHash p
computeHash Genesis = GenesisFn ()
computeHash (block1 >>= fn) = computeHash (fn (getPayload block1))

namespace Blockchain
  ||| This blockchain allows heterogeneous blocks with different payloads and different
  ||| (payload dependent) hashing algorithms.  
  ||| The crypto-correctness of the chain is guaranteed by the type.
  |||
  ||| This blockchain maintains the 'running' last block hash
  ||| @ payloads the type level list of payload types does not buy me much except for 
  ||| having a simple extractPayloads function
  data Blockchain : (payloads : List Type) -> BlockHash -> Type where
       Single : Block () 0 GenesisFn -> Blockchain [()] (GenesisFn ())
       (::) : (block : Block a h1 hash_fn) -> Blockchain ax h1 -> Blockchain (a::ax) (hash_fn (getPayload block))

extractPayloads : Blockchain payloads hs -> HList payloads 
extractPayloads (Single g) = () :: HNil
extractPayloads (block :: chain) =  (getPayload block) :: extractPayloads chain

extractPrevHashes : Blockchain payloads hs -> List BlockHash 
extractPrevHashes (Single g) = [0]
extractPrevHashes (block :: chain) = (extractPrevHash block) :: extractPrevHashes chain

computeHashes : Blockchain payloads hs -> List BlockHash 
computeHashes (Single g) = [GenesisFn ()]
computeHashes (block :: chain) = (computeHash block) :: computeHashes chain

-------------------------------
-- Examples
-- for example usage see `Test.Blockchain` module
-------------------------------
exampleMiner : BlockData a => (payload : a) -> Blockchain ax (prevHash payload) -> Blockchain (a :: ax) (blockHash payload)
exampleMiner payload chain =  (MkBlock payload) :: chain 
