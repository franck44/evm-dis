
object "Runtime" {
  code {
    let r := 1
    for { let i := 0 } lt(i, 10) { } {
        for { let k := 0 } lt(k, 10) { } {
            r := mul(r, 2) 
          }
        r := add(r, 1) 
      }
    mstore(0x40, r)
    return(0x40, 32)
  }
}

