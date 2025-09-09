// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from 'forge-std/Test.sol';
import {MyTokenBank} from '../src/Token/MyTokenBank.sol';
import {MyToken} from '../src/Token/MyToken.sol';
import {SigUtils} from '../src/utils/SigUtils.sol';
import '@openzeppelin/contracts/utils/Strings.sol';

contract MyTokenTest is Test {
    MyToken public token;
    MyTokenBank public tokenBank;
    SigUtils sigUtils;
    uint256 ownerPrivateKey;

    function setUp() public {
        token = new MyToken();
        sigUtils = new SigUtils(token.DOMAIN_SEPARATOR());
    }

    function testPermit() public {
        (address owner, uint256 pKey) = makeAddrAndKey('owner');
        ownerPrivateKey = pKey;
        address spender = makeAddr('spender');
        SigUtils.Permit memory permit = SigUtils.Permit({
            owner: owner,
            spender: spender,
            value: 1e18,
            nonce: 0,
            deadline: 1 days
        });
        console.log('owner is:', address(owner));
        console.log('spender is:', address(spender));
        bytes32 digest = sigUtils.getTypedDataHash(permit);

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerPrivateKey, digest);

        vm.startPrank(owner);
        console.log('owner is:', address(owner));
        console.log('spender is:', address(spender));
        console.log('msgsender is:', address(msg.sender));
        token.permit(
            permit.owner,
            permit.spender,
            permit.value,
            permit.deadline,
            v,
            r,
            s
        );
        assertEq(token.allowance(owner, spender), permit.value);
        vm.stopPrank();
    }
}
