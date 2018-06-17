module Test.Blockchain

import Test.Asserts
import Data.Hash
import Blockchain

%access export  

||| Simple tests use Nat type
Hashable Nat where
   saltedHash64 n = saltedHash64 (toIntegerNat n)

||| Simplified test blocks containing integers that can be only placed consecutively 
||| on the blockchain `n :: (n - 1) :: ... :: 1 :: 0 :: Genesis`
record TestNatPayload where
       constructor MkTestNatPayload
       payload : Nat

Show TestNatPayload where
   show = show . payload

Cast TestNatPayload Nat where
   cast = payload 

||| assumes i can only be linked to (i - 1)
hashPrevNat : Nat -> BlockHash
hashPrevNat Z = GenesisHash
hashPrevNat (S i) = hash . show $ i

||| ignoring serialization
BlockData TestNatPayload where
   serialize = show 
   prevHash = hashPrevNat . payload

||| Note this is very tightly typed requiring consecutive numbers so stuff like this 
||| ```idris example
|||  natChain1 : HBlockchain [TestNatPayload, TestNatPayload, ()] (blockHash (MkTestNatPayload 1))
|||  natChain1 = exampleMiner (MkTestNatPayload 1) (exampleMiner (MkTestNatPayload 1) (Single Genesis))
||| ```
|||will not compile
natChain : HBlockchain [TestNatPayload, TestNatPayload] (blockHash (MkTestNatPayload 1))
natChain = exampleMiner (MkTestNatPayload 1) (exampleMiner (MkTestNatPayload 0) (Single Block.Genesis))

testNatHashes : IO ()
testNatHashes = 
      assertEq ((take 2) . computeHashes $ natChain) (map (hash . show) $ [1,0])  

testNatPayloads : IO ()
testNatPayloads = 
    assertEq (the (List Nat) (asList $ natChain)) [1,0]

||| Again note this is very tightly typed, for example this will not compile
||| ```idris example
|||  natSimpleChain = (MkTestNatPayload 1) :: (MkTestNatPayload 1) :: SimpleBlockchain.Genesis
||| ```
natSimpleChain : SimpleBlockchain TestNatPayload (blockHash (MkTestNatPayload 1))
natSimpleChain = (MkTestNatPayload 1) :: (MkTestNatPayload 0) :: SimpleBlockchain.Genesis

extractSimpleHash : SimpleBlockchain a hash -> BlockHash 
extractSimpleHash {hash} block = hash 

testNatSimpleHash : IO () 
testNatSimpleHash = 
   assertEq (extractSimpleHash natSimpleChain) (hash . show $ 1)


||| Simplified test msg block
record MsgPayload where
       constructor MkMsgPayload
       prevMsgHash : BlockHash
       msg : String

Show MsgPayload where
   show block = (show . prevMsgHash $ block) ++ ":" ++ (msg block)

BlockData MsgPayload where
   serialize = show 
   prevHash = prevMsgHash

||| Attempting to compile the following never returns with Idris 1.2:
||| ```idris example
|||  msgChain : SimpleBlockchain MsgPayload (strHash "16FC397CF62F64D3:Hello")
|||  msgChain = (MkMsgPayload GenesisHash "Hello") :: SimpleBlockchain.Genesis
||| ```
||| I do not expect to have much use of hardcoded values of hash type variable
||| this works 
msgSimpleChain1 : (h ** SimpleBlockchain MsgPayload h)
msgSimpleChain1 = (_ ** (MkMsgPayload GenesisHash "Hello") :: SimpleBlockchain.Genesis)

testMsgSimpleChain1Hash : IO()
testMsgSimpleChain1Hash =
   case msgSimpleChain1 of 
        (h ** _) => assertEq h (strHash $ (show GenesisHash) ++ ":Hello") 


mixedChain : (h ** HBlockchain [MsgPayload, TestNatPayload] h)
mixedChain = (_ ** exampleMiner (MkMsgPayload (strHash "0") "Hello") (exampleMiner (MkTestNatPayload 0) (Single Block.Genesis)))

testMixedChainHash : IO()
testMixedChainHash =
   case mixedChain of 
        (h ** _) => assertEq h (strHash (show (strHash "0") ++ ":Hello")) 
