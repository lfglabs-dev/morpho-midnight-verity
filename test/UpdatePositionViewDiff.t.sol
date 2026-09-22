// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity 0.8.34;

import {Test} from "forge-std/Test.sol";
import {stdJson} from "forge-std/StdJson.sol";
import {Midnight} from "../vendor/midnight/src/Midnight.sol";
import {Market} from "../vendor/midnight/src/interfaces/IMidnight.sol";

/// Calls the original `Midnight.updatePositionView` on storage prepared from
/// `test/vectors.json`. It does not reimplement the arithmetic.
contract UpdatePositionViewDiffTest is Test {
    using stdJson for string;

    Midnight internal midnight;
    bytes32 internal constant ID = bytes32(uint256(1));
    address internal constant USER = address(2);

    function setUp() public {
        midnight = new Midnight();
    }

    function _positionBase() internal pure returns (bytes32) {
        bytes32 inner = keccak256(abi.encode(ID, uint256(0)));
        return keccak256(abi.encode(USER, inner));
    }

    function _marketBase() internal pure returns (bytes32) {
        return keccak256(abi.encode(ID, uint256(1)));
    }

    function _store(uint256 credit, uint256 pending, uint256 lossFactor, uint256 lastLoss, uint256 lastAccrual)
        internal
        returns (bytes32 pos0, bytes32 pos1, bytes32 mkt0)
    {
        pos0 = bytes32(credit | (pending << 128));
        pos1 = bytes32(lastLoss | (lastAccrual << 128));
        mkt0 = bytes32(lossFactor << 128);
        bytes32 base = _positionBase();
        vm.store(address(midnight), base, pos0);
        vm.store(address(midnight), bytes32(uint256(base) + 1), pos1);
        vm.store(address(midnight), _marketBase(), mkt0);
    }

    function test_vectors() public {
        string memory json = vm.readFile("test/vectors.json");
        uint256 n = 0;
        while (true) {
            try vm.parseJsonString(json, string.concat("[", vm.toString(n), "].name")) returns (string memory) {
                n++;
            } catch {
                break;
            }
        }
        string memory out;
        for (uint256 i = 0; i < n; i++) {
            string memory p = string.concat("[", vm.toString(i), "]");
            string memory name = json.readString(string.concat(p, ".name"));
            uint256 credit = vm.parseUint(json.readString(string.concat(p, ".credit")));
            uint256 pending = vm.parseUint(json.readString(string.concat(p, ".pending")));
            uint256 lossFactor = vm.parseUint(json.readString(string.concat(p, ".lossFactor")));
            uint256 lastLoss = vm.parseUint(json.readString(string.concat(p, ".lastLoss")));
            uint256 lastAccrual = vm.parseUint(json.readString(string.concat(p, ".lastAccrual")));
            uint256 timestamp = vm.parseUint(json.readString(string.concat(p, ".timestamp")));
            uint256 maturity = vm.parseUint(json.readString(string.concat(p, ".maturity")));
            (bytes32 pos0, bytes32 pos1, bytes32 mkt0) = _store(credit, pending, lossFactor, lastLoss, lastAccrual);
            vm.warp(timestamp);
            Market memory market;
            market.maturity = maturity;
            try midnight.updatePositionView(market, ID, USER) returns (uint128 a, uint128 b, uint128 c) {
                out = string.concat(out, name, " ok ", vm.toString(a), " ", vm.toString(b), " ", vm.toString(c), "\n");
            } catch {
                out = string.concat(out, name, " revert\n");
            }
            bytes32 base = _positionBase();
            assertEq(vm.load(address(midnight), base), pos0, name);
            assertEq(vm.load(address(midnight), bytes32(uint256(base) + 1)), pos1, name);
            assertEq(vm.load(address(midnight), _marketBase()), mkt0, name);
        }
        vm.writeFile("out/solidity-results.txt", out);
    }
}
