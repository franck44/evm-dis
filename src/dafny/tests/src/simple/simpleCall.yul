
object "Runtime" {
  code {

  function foo1(x)  -> r
  {
    r := x
  }

  function foo2(x) -> r
  {
    r := foo1(x)
  }
      
  let x := 8

  let z := foo1(x)

  mstore(0x40, z)
  return(0x40, 32)
  }
}
