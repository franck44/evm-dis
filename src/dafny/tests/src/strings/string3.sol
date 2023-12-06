// SPDX-License-Identifier: MIT

pragma solidity >= 0.8.0 ;

contract K {

    // bytes name;
    
    bytes[] public l;

       function updateName(bytes calldata _name) external {
        // name = _name;

        
        // Usurp the current monarch, replacing them with the new one.
        l.push(_name);
        // currentMonarch = Monarch(
        //     // msg.sender,
        //     "Albert"
        //     // valuePaid,
        //     // block.timestamp
        // );

       
    }

  
}
