import stainless.collection._

def sumTo(n: BigInt): BigInt =
  require(0 <= n)
  if n == 0 then BigInt(0)
  else n + sumTo(n-1)    

def sumToIsCorrect(n: BigInt): Unit = {
  require(0 <= n)
  if n == 0 then ()
  else sumToIsCorrect(n-1)
} ensuring { _ => sumTo(n) == n*(n+1)/2 }
