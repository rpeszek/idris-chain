module Test.Blockchain

import Test.Asserts
import Data.Hash
import Blockchain

%access export  

||| Convenient to use Nat as ha
Hashable Nat where
   saltedHash64 n = saltedHash64 (toIntegerNat n)

||| Simplified test blocks containing integers that can be only placed consecutively 
||| on the blockchain `n :: (n - 1) :: ... :: 1 :: 0 :: Genesis`
record TestNatBlock where
       constructor MkTestNatBlock
       payload : Nat

Show TestNatBlock where
   show = show . payload

||| assumes i can only be linked to (i - 1)
hashPrevNat : Nat -> BlockHash
hashPrevNat Z = GenesisHash
hashPrevNat (S i) = hash . show $ i

||| ignoring serialization
BlockData TestNatBlock where
   serialize = show 
   prevHash = hashPrevNat . payload

||| Note this is very tightly typed requiring consecutive numbers so stuff like this 
||| ```idris example
|||  natChain1 : HBlockchain [TestNatBlock, TestNatBlock, ()] (blockHash (MkTestNatBlock 1))
|||  natChain1 = exampleMiner (MkTestNatBlock 1) (exampleMiner (MkTestNatBlock 1) (Single Genesis))
||| ```
|||will not compile
natChain : HBlockchain [TestNatBlock, TestNatBlock, ()] (blockHash (MkTestNatBlock 1))
natChain = exampleMiner (MkTestNatBlock 1) (exampleMiner (MkTestNatBlock 0) (Single Block.Genesis))

testHashes : IO ()
testHashes = 
      assertEq ((take 2) . computeHashes $ natChain) (map (hash . show) $ [1,0])  

testPayloads : IO ()
testPayloads = 
    assertEq (show . extractPayloads $ natChain) ("1::0::()::HNil")

||| Again note this is very tightly typed, for example this will not compile
||| ```idris example
|||  natSimpleChain = (MkTestNatBlock 1) :: (MkTestNatBlock 1) :: SimpleBlockchain.Genesis
||| ```
natSimpleChain : SimpleBlockchain TestNatBlock (blockHash (MkTestNatBlock 1))
natSimpleChain = (MkTestNatBlock 1) :: (MkTestNatBlock 0) :: SimpleBlockchain.Genesis

extractSimpleHash : SimpleBlockchain a hash -> BlockHash 
extractSimpleHash {hash} block = hash 

testSimpleHash : IO () 
testSimpleHash = 
   assertEq (extractSimpleHash natSimpleChain) (hash . show $ 1)


||| Simplified test msg block
record MsgBlock where
       constructor MkMsgBlock
       prevMsgHash : BlockHash
       msg : String

Show MsgBlock where
   show block = (show . prevMsgHash $ block) ++ ":" ++ (msg block)

BlockData MsgBlock where
   serialize = show 
   prevHash = prevMsgHash

||| Attempting to compile the following never returns with Idris 1.2:
||| ```idris example
|||  msgChain : SimpleBlockchain MsgBlock (strHash "16FC397CF62F64D3:Hello")
|||  msgChain = (MkMsgBlock GenesisHash "Hello") :: SimpleBlockchain.Genesis
||| ```
||| I do not expect to have much use of hardcoded values of hash type variable
||| this works 
msgSimpleChain1 : (h ** SimpleBlockchain MsgBlock h)
msgSimpleChain1 = (_ ** (MkMsgBlock GenesisHash "Hello") :: SimpleBlockchain.Genesis)

testMsgSimpleChain1Hash : IO()
testMsgSimpleChain1Hash =
   case msgSimpleChain1 of 
        (h ** _) => assertEq h (strHash "16FC397CF62F64D3:Hello") 


mixedChain : (h ** HBlockchain [MsgBlock, TestNatBlock, ()] h)
mixedChain = (_ ** exampleMiner (MkMsgBlock (strHash "0") "Hello") (exampleMiner (MkTestNatBlock 0) (Single Block.Genesis)))

testMixedChain1Hash : IO()
testMixedChain1Hash =
   case mixedChain of 
        (h ** _) => assertEq h (strHash (show (strHash "0") ++ ":Hello")) 
