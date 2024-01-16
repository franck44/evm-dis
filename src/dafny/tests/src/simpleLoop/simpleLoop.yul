
object "Runtime" {
  code {
    let r := 0
    for { let i := 0 } lt(i, 10) { } {
        r := add(r, 1) 
    }
    mstore(0x40, r)
    return(0x40, 32)
  }
}

