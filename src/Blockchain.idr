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
   It does not implement anything else (P2P networking, payloads stored in chain, etc).
-}

------------------------------
--- HList needed as a utilitity
------------------------------
namespace HList
  infixr 7 ::
  data HList : List Type -> Type where
    HNil : HList []
    (::) : t -> HList ts -> HList (t :: ts)


--------------------
-- DSL
--------------------

BlockHash : Type
BlockHash = Bits64

GenesisFn : () -> BlockHash 
GenesisFn = hash -- (const (hash ())) 

||| `Block payload hash hash_fn` looks like a dependently typed indexed monad.
||| For simplicity, the payload is assumed to store hash of the linked block
|||  @ payload payload type 
|||  @ hash links previous block
|||  @ hash_fn hash function that knows how to sign the payload
data Block : (payload : Type) -> (hash: BlockHash) -> (hash_fn : payload -> BlockHash) -> Type where
    ||| To be cryptgraphically kosher payload needs to include linked block hash information 
    ||| represented here as `extract_fn`, `sig` knows how to sign the payload
    ||| A possibly more straightforward idea is to introduce a BlockHeader 
    ||| record that is hashing friendly/Hashable instead of `extract_fn`.
    ||| @ payload 
    ||| @ extract_fn when applied to payload extract hash of linked block
    ||| @ sig function that computes hash of this payload
    MkBlock : (payload : a) -> (extract_fn : a -> BlockHash) -> (sig : a -> BlockHash) -> Block a (extract_fn payload) sig
    
    Genesis : Block () 0 GenesisFn 
    ||| This is currently not used, 
    ||| monadic function verifies previous payload (payload : a) and exposes proof of that verification
    ||| (hash2_fn payload) as well as provides hash function that works on its own payload.
    (>>=) : Block a hash1 hash2_fn ->
            ((payload : a) -> Block b (hash2_fn payload) hash3_fn) ->
            Block b (hash2_fn payload) hash3_fn

getPayload : Block a h hash_fn -> a
getPayload (MkBlock p ef hf) = p
getPayload Genesis = ()
getPayload (block1 >>= fn) = getPayload (fn (getPayload block1))

extractHash : Block a h hash_fn -> BlockHash
extractHash (MkBlock p ef hf) = ef p
extractHash Genesis = 0
extractHash (block1 >>= fn) = extractHash (fn (getPayload block1))

computeHash : Block a h hash_fn -> BlockHash
computeHash (MkBlock p ef hf) = hf p
computeHash Genesis = GenesisFn ()
computeHash (block1 >>= fn) = computeHash (fn (getPayload block1))

||| This blockchain allows heterogeneous blocks with different payloads and different
||| (payload dependent) hashing algorithms.  
||| The crypto-correctness of the chain is guaranteed by the type.
|||
||| This blockchain maintains the 'running' last block hash
||| @ payloads the type level list of payload types does not buy me much except for 
||| having a simple extractPayloads function
data Blockchain : (payloads : List Type) -> BlockHash -> Type where
     BNil : Block () 0 GenesisFn -> Blockchain [()] (GenesisFn ())
     (::) : (block : Block a h1 hash_fn) -> Blockchain ax h1 -> Blockchain (a::ax) (hash_fn (getPayload block))

extractPayloads : Blockchain payloads hs -> HList payloads 
extractPayloads (BNil g) = () :: HNil
extractPayloads (block :: chain) =  (getPayload block) :: extractPayloads chain

extractHashes : Blockchain payloads hs -> List BlockHash 
extractHashes (BNil g) = [0]
extractHashes (block :: chain) = (extractHash block) :: extractHashes chain

computeHashes : Blockchain payloads hs -> List BlockHash 
computeHashes (BNil g) = [GenesisFn ()]
computeHashes (block :: chain) = (computeHash block) :: computeHashes chain

-------------------------------
-- examples, TODO setup package management and move this to tests
-------------------------------
exampleMiner : Hashable a => (extract_fn : a -> BlockHash) -> (payload : a) -> Blockchain ax (extract_fn payload) -> Blockchain (a :: ax) (hash payload)
exampleMiner extract_fn payload chain =  (MkBlock payload extract_fn hash) :: chain 

||| assumes i is linked to (i - 1)
testExtract : Int -> BlockHash
testExtract 1 = GenesisFn ()
testExtract i = hash (i - 1)

test : List BlockHash 
test =  
     let chain = exampleMiner testExtract 2 (exampleMiner testExtract 1 (BNil Genesis))
     in computeHashes chain 

{- repl:
*Blockchain> map (prim__zextB64_BigInt) test
[18324063653670288597, 10229930702868701396, 1656261971834528979] : List Integer
*Blockchain> map (prim__zextB64_BigInt . hash) [2,1]
[18324063653670288597, 10229930702868701396] : List Integer
-}

test2 : HList [Int, Int, ()] 
test2 =  
     let chain = exampleMiner testExtract 2 (exampleMiner testExtract 1 (BNil Genesis))
     in extractPayloads chain 
