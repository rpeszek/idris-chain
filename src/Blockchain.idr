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


--------------------
-- DSLs
--------------------

BlockHash : Type
BlockHash = Bits64

GenesisHash : Bits64
GenesisHash = hash () 

GenesisFn : () -> BlockHash 
GenesisFn = hash -- (const (hash ())) 

||| Conceptual code does not want to concern itself with particulars
||| of how this is done
interface BlockData a where
    myHash : a -> BlockHash 
    prevHash : a -> BlockHash

--------------------------------
-- Simple homogenious blockchain 
--------------------------------

namespace SimpleBlockchain
  data SimpleBlockchain : (payload : Type) -> (hash : BlockHash) -> Type where 
     Genesis : SimpleBlockchain a GenesisHash
     (::) : BlockData a => (payload : a) -> SimpleBlockchain a (prevHash payload) -> SimpleBlockchain a (myHash payload) 

--------------------------------------------------
-- Heterogenous blockchain with varying payloads 
-- Can blockchain be general purpose and store various types of payloads?
-------------------------------------------------- 

-- TODO this is getting better but still needs more thinking

||| `Block payload hash hash_fn` looks like standard dependently typed indexed monad.
|||  @ payload that contains previous hash and can be hashed (satisfies BlockData contraint) 
|||  @ hash links previous block
|||  @ hash_fn hash function that knows how to sign the payload
data Block : (payload : Type) -> (hash: BlockHash) -> (hash_fn : payload -> BlockHash) -> Type where
    MkBlock : BlockData a => (payload : a) -> Block a (prevHash payload) myHash
    
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
computeHash (MkBlock p) = myHash p
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

extractPrevHashes : Blockchain payloads hs -> List BlockHash 
extractPrevHashes (BNil g) = [0]
extractPrevHashes (block :: chain) = (extractPrevHash block) :: extractPrevHashes chain

computeHashes : Blockchain payloads hs -> List BlockHash 
computeHashes (BNil g) = [GenesisFn ()]
computeHashes (block :: chain) = (computeHash block) :: computeHashes chain

-------------------------------
-- examples, TODO setup package management and move this to tests
-------------------------------
exampleMiner : BlockData a => (payload : a) -> Blockchain ax (prevHash payload) -> Blockchain (a :: ax) (myHash payload)
exampleMiner payload chain =  (MkBlock payload) :: chain 

||| assumes i is linked to (i - 1)
testPrevInt : Int -> BlockHash
testPrevInt 1 = GenesisHash
testPrevInt i = hash (i - 1)

||| assumes i is linked to (i - 1)
BlockData Int where
   myHash i = hash i
   prevHash = testPrevInt

testSimple : SimpleBlockchain Int (myHash (the Int 2))
testSimple = (the Int 2) :: (the Int 1) :: SimpleBlockchain.Genesis

test : List BlockHash 
test =  
     let chain = exampleMiner (the Int 2) (exampleMiner (the Int 1) (BNil Genesis))
     in computeHashes chain 

{- repl:
*Blockchain> map (prim__zextB64_BigInt) test
[18324063653670288597, 10229930702868701396, 1656261971834528979] : List Integer
*Blockchain> map (prim__zextB64_BigInt . hash) [2,1]
[18324063653670288597, 10229930702868701396] : List Integer
-}

test2 : HList [Int, Int, ()] 
test2 =  
     let chain = exampleMiner (the Int 2) (exampleMiner (the Int 1) (BNil Genesis))
     in extractPayloads chain 
