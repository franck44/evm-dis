
object "Runtime" {
  code {

    function max(x, y) -> result
    {
        result := x
        if lt(x, y) {
            result := y
        }
    }

    function iter(x) -> result
    {
        result := 0
        for { let k := 0 } lt(k, x) { k := add(k, 1)} {
            result := max(result, x) 
          }
    }

    let r := 0
    for { let j := 0} lt(j, 12) { j := add(j, 1) } {
        r := iter(12)
        r := iter(r)
    }
    

    mstore(0x40, r)
    return(0x40, 32)

  }
}

