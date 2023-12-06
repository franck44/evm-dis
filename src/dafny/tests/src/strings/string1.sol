// SPDX-License-Identifier: MIT

pragma solidity >=0.8.0;

contract K {
    string name;

    struct S {
        string name;
    }

    S var1;

    function updateName(string calldata _name) external {
        name = _name;
        var1 = S(_name);

    }
}
