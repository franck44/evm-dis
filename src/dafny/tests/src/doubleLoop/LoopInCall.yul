
object "Runtime" {
  code {

    function iter(x) -> result
    {
        result := 0
        for { let k := 0 } lt(k, x) { } {
            result := add(result, 1) 
          }
    }
    let r := iter(12)
    r := iter(10)

    mstore(0x40, r)
    return(0x40, 32)

  }
}

