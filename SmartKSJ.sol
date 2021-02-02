//SPDX-License-Identifier: UNLICENSED
/**
 *Submitted for verification at Etherscan.io on 2020-08-26
*/

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol



pragma solidity ^0.6.12;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

library Address {
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


library EnumerableSet {
    struct Set {
        // Storage of set values
        bytes32[] _values;

        // Position of the value in the `values` array, plus 1 because index 0
        // means a value is not in the set.
        mapping (bytes32 => uint256) _indexes;
    }

    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            // The value is stored at length-1, but we add 1 to all indexes
            // and use 0 as a sentinel value
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    function _remove(Set storage set, bytes32 value) private returns (bool) {
        // We read and store the value's index to prevent multiple reads from the same storage slot
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) { // Equivalent to contains(set, value)
            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            // When the value to delete is the last one, the swap operation is unnecessary. However, since this occurs
            // so rarely, we still do the swap anyway to avoid the gas cost of adding an 'if' statement.

            bytes32 lastvalue = set._values[lastIndex];

            // Move the last value to the index where the value to delete is
            set._values[toDeleteIndex] = lastvalue;
            // Update the index for the moved value
            set._indexes[lastvalue] = toDeleteIndex + 1; // All indexes are 1-based

            // Delete the slot where the moved value was stored
            set._values.pop();

            // Delete the index for the deleted slot
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._indexes[value] != 0;
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        require(set._values.length > index, "EnumerableSet: index out of bounds");
        return set._values[index];
    }

    // AddressSet

    struct AddressSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(value)));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(value)));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(value)));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint256(_at(set._inner, index)));
    }


    // UintSet

    struct UintSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }
}

// File: @openzeppelin/contracts/GSN/Context.sol

abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

contract ERC20 is Context, IERC20 {
    using SafeMath for uint256;
    using Address for address;

    mapping (address => uint256) private _balances;

    mapping (address => mapping (address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;
    uint8 private _decimals;

    /**
     * @dev Sets the values for {name} and {symbol}, initializes {decimals} with
     * a default value of 18.
     *
     * To select a different value for {decimals}, use {_setupDecimals}.
     *
     * All three of these values are immutable: they can only be set once during
     * construction.
     */
    constructor (string memory name, string memory symbol) public {
        _name = name;
        _symbol = symbol;
        _decimals = 18;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5,05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless {_setupDecimals} is
     * called.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view returns (uint8) {
        return _decimals;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20};
     *
     * Requirements:
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address sender, address recipient, uint256 amount) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(address sender, address recipient, uint256 amount) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(sender, recipient, amount);

        _balances[sender] = _balances[sender].sub(amount, "ERC20: transfer amount exceeds balance");
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements
     *
     * - `to` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        _balances[account] = _balances[account].sub(amount, "ERC20: burn amount exceeds balance");
        _totalSupply = _totalSupply.sub(amount);
        emit Transfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner`s tokens.
     *
     * This is internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Sets {decimals} to a value other than the default one of 18.
     *
     * WARNING: This function should only be called from the constructor. Most
     * applications that interact with token contracts will not expect
     * {decimals} to ever change, and may work incorrectly if it does.
     */
    function _setupDecimals(uint8 decimals_) internal {
        _decimals = decimals_;
    }

    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual { }
}

contract SmartKSJ  {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;
    address public owner;
    address public datastore;
    address public pairAddr;
    address public usdtAddr;
    uint256 public ksjPerSec = 115740740740740740;
    uint public oneEth = 1 ether;
    bool public isFlag = false;
    uint public oneUsdt = 1000000;
    

    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyWithdraw(address indexed user, uint256 indexed pid, uint256 amount);

    constructor() public {
        owner = msg.sender;
    }
    modifier onlyOwner(){
        require(owner == msg.sender);
        _;
    }
    function transferOwnerShip(address _owner) public onlyOwner{
        owner = _owner;
    }
    function setFlga(bool _isFlag) public onlyOwner{
        isFlag = _isFlag;
    }
    function setInit(address _pairAddr, address _usdtAddr,address _datastore) public onlyOwner {
        pairAddr = _pairAddr;
        datastore = _datastore;
        usdtAddr = _usdtAddr;
    }

    //用户查看收益
    function pendingKSJ(uint256 _pid, address _user) public view returns (uint256,uint) {
        uint staticReward = viewStaticReward(_pid,_user);
        uint dynamicReward = viewDynamicReward(_user);
        return (staticReward,dynamicReward);
    }
    //查看静态收益
    function viewStaticReward(uint _pid,address _user) public view returns(uint){
        uint staticReward;
        for(uint i=0;i< IKsjDataStore(datastore).viewDepositPidCount(_pid,_user) ;i++){
            uint idD = IKsjDataStore(datastore).depositPidCount(_pid,_user,i);
            staticReward = staticReward.add( viewDepStaticRDtime(_pid,_user,idD));
        }
        return staticReward;
    }
    
    function viewDepStaticRDtime(uint _pid,address _user,uint _dtime) public view returns(uint){
        (
        address lpToken,           // Address of LP token contract.
        uint256 allocPoint,       // How many allocation points assigned to this pool. ksjs to distribute per block.
        uint256 lastRewardTime,  // Last block number that ksjs distribution occurs.
        uint256 accKSJPerShare, ,,) = IKsjDataStore(datastore).poolInfo(_pid);
        
        uint256 lpSupply = IERC20(lpToken).balanceOf(datastore);
        if (block.timestamp > lastRewardTime && lpSupply != 0) {
            uint256 ksjReward = (block.timestamp.sub(lastRewardTime)).mul(ksjPerSec).mul(allocPoint).div(IKsjDataStore(datastore).totalAllocPoint());
            accKSJPerShare = accKSJPerShare.add(ksjReward.mul(4500).mul(1e12).div(lpSupply).div(10000));
            (uint256 amount,uint rewardDebt)  = IKsjDataStore(datastore).getDepositAmount(_pid,_user,_dtime);
            return amount.mul(accKSJPerShare).div(1e12).sub(rewardDebt);
        }
        return uint(0);
    }

    //查看动态收益
    function viewDynamicReward(address _user) public view returns(uint){
        (,,,,uint dynamicAmount,        
        uint rewardDebt,uint totalInvest,,,,) = IKsjDataStore(datastore).userInfo(_user);
        if(totalInvest>0){
            return dynamicAmount.mul(IKsjDataStore(datastore).dynamicPerShare()).div(1e12).sub(rewardDebt) ;
        }
        return uint(0);
    }
    //更新矿池
    function updatePool(uint256 _pid) public {
        (
        address lpToken,           // Address of LP token contract.
        uint256 allocPoint,       // How many allocation points assigned to this pool. ksjs to distribute per block.
        uint256 lastRewardTime,,,,) = IKsjDataStore(datastore).poolInfo(_pid);
        
        if (block.timestamp <= lastRewardTime) {
            return;
        }
        uint256 lpSupply = IERC20(lpToken).balanceOf(datastore);
        if (lpSupply == 0) {
            IKsjDataStore(datastore).setPool(_pid,0);
            return;
        }
        uint totalAllocPoint = IKsjDataStore(datastore).totalAllocPoint();
        uint256 ksjReward = (block.timestamp.sub(lastRewardTime)).mul(ksjPerSec).mul(allocPoint).div(totalAllocPoint);
        IKsjDataStore(datastore).setPool(_pid,ksjReward);
    }
   
    event getRLog(address,uint reward,uint dynamic,uint pending);
    event getRlogs2(uint pending,uint dynamic);
    //用户提取收益
    function getReward(uint _pid) public {
        
        (,,, uint256 accKSJPerShare,,,) = IKsjDataStore(datastore).poolInfo(_pid);
        uint pending ;
        for(uint i=0;i< IKsjDataStore(datastore).viewDepositPidCount(_pid,msg.sender) ;i++){
            uint idD = IKsjDataStore(datastore).depositPidCount(_pid,msg.sender,i);
            pending = pending.add( viewDepStaticRDtime(_pid,msg.sender,idD));
            IKsjDataStore(datastore).updateDepositDebt( _pid,msg.sender,idD);
        }
        
        uint dynamic = viewDynamicReward(msg.sender);
        emit getRlogs2(pending,dynamic);
        uint rewards = pending.add(dynamic);
        require(pending>0);
        IKsjDataStore(datastore).safeSendKsj(msg.sender,rewards);
        IKsjDataStore(datastore).updateUser(msg.sender,address(0),0,IKsjDataStore(datastore).dynamicPerShare(), 0,0,0);
        IKsjDataStore(datastore).updateUserTotal(msg.sender,pending,dynamic);
        emit getRLog(msg.sender,rewards,dynamic,pending);
        
        updateActDyAmount( pending,msg.sender,_pid,accKSJPerShare);
        
        (,address invitor, uint level,,,,,,,,) = IKsjDataStore(datastore).userInfo(msg.sender);
        excuteMore( _pid,invitor, 1, 0,rewards,0,level,0);
        updatePool(_pid);
    }
    event LogI(address,uint,uint,uint);
    //更新1代动态算力
    function updateActDyAmount(uint _pending,address _user,uint _pid,uint accKSJPerShare) private {
        address _firstInvitor = IKsjDataStore(datastore).getInvitor(_user);
        uint lenI = IKsjDataStore(datastore).viewDepositPidCount(_pid,_firstInvitor);
        uint pendingI ;
        for(uint i=0;i< lenI ;i++){
            uint idD = IKsjDataStore(datastore).depositPidCount(_pid,_firstInvitor,i);
            ( uint256 amount, uint256 rewardDebt, ,,) = IKsjDataStore(datastore).depositInfo(_pid,_firstInvitor,idD);
            uint pendingR = amount.mul(accKSJPerShare).div(1e12).sub(rewardDebt);
            pendingI = pendingI.add(pendingR);
        }
        
        uint rewardAm_fir = pendingI > _pending ? _pending : pendingI;
        uint dy1 = rewardAm_fir.mul(2000).div(10000);
        IKsjDataStore(datastore).updateUser(_firstInvitor,address(0), dy1,0, 0,0,0);
        emit LogI(_firstInvitor,_pending,pendingI,dy1);
    }

    //用户充值lp
    function deposit(uint256 _pid, uint256 _inputAmount, address _invitor) public {
        
        uint len = IKsjDataStore(datastore).viewDepositPidCount(_pid,msg.sender);
        (uint regitsTime,,,,,,,,,,) = IKsjDataStore(datastore).userInfo(_invitor);
        (address lpToken,,,, ,uint limitUsdt,uint curUsdtVal) = IKsjDataStore(datastore).poolInfo(_pid);
        (,, uint level,,,,,,,,uint totalInvestUsdt) = IKsjDataStore(datastore).userInfo(msg.sender);
        require(curUsdtVal < limitUsdt);
        require(regitsTime > 0);//推荐人已经注册过
        require(_inputAmount > 0);
        require(len < 5);//单个地址在该矿池充值次数<=5
        (uint _amount,uint _usdtAm ) = remainingLimit(_pid,_inputAmount);
        require(_amount > 0);
        require(_usdtAm >= oneUsdt.mul(200));
        require(totalInvestUsdt <= oneUsdt.mul(6000));
        
        IERC20(lpToken).safeTransferFrom(address(msg.sender), address(datastore), _amount);
        IKsjDataStore(datastore).setDeposit( _pid, msg.sender,0, _amount,_usdtAm,1) ;
        IKsjDataStore(datastore).updateUser(msg.sender, _invitor,0,1, _usdtAm ,_amount,1);
        
        IKsjDataStore(datastore).updatePoolUsdt( _pid, _usdtAm ,1);
        updatePool(_pid);
        
        excuteMore(_pid, _invitor, 1, _amount,0,0, level,1);
        emit Deposit(msg.sender, _pid, _amount);
    }

    //查看单个地址当前充值总额


    

    function excuteMore(uint _pid,address _invitor,uint _times,uint _lp,uint _rewards,uint _actRate,uint _lastLevel,uint _indexId) private {
        if(_times <=8 && _lp > 0 &&  _invitor != address(0) && _invitor != IKsjDataStore(datastore).sysAddr()){            
            IKsjDataStore(datastore).updateTeamLp( _pid, _invitor,  _lp, _indexId);
            (,address invitor, uint level,,,,,,,,) = IKsjDataStore(datastore).userInfo(_invitor);
            if(_rewards > 0){
                _actRate = getActRate(level,_lastLevel,_actRate);
                uint newDy = _actRate.mul(_rewards).div(10000);
                IKsjDataStore(datastore).updateUser(_invitor,address(0), newDy,0, 0,0,0);
            }
            excuteMore(_pid, invitor, _times+1,_lp, _rewards,_actRate, level,_indexId);
        }
    }

    function getActRate(uint _level2,uint _level1,uint _rate1) public view returns(uint){
        if(_level2 > _level1){
            uint l2 = IKsjDataStore(datastore).levelRate(_level2);
            uint l1 = IKsjDataStore(datastore).levelRate(_level1);
            return l2.sub(l1);
        }else if(_level2 == _level1){
            return _rate1.div(10);
        }
        return uint(0);
    }
    

    // 用户提取lp
    function withdraw(uint256 _pid ,uint _dtimes) public {
        updatePool(_pid);

        (address lpToken,,, uint256 accKSJPerShare,,,) = IKsjDataStore(datastore).poolInfo(_pid);
        (uint256 amount, uint256 rewardDebt,, uint endTime,uint amountU ) = IKsjDataStore(datastore).depositInfo(_pid,msg.sender,_dtimes);
        
        require( amount >= 0 , "withdraw: not good");

        if(block.timestamp >= endTime){
            IKsjDataStore(datastore).safeSendLp(lpToken,msg.sender,amount);
        }else{
            IKsjDataStore(datastore).safeSendLp(lpToken,msg.sender,amount.mul(95).div(100));
            IKsjDataStore(datastore).safeSendLp(lpToken,IKsjDataStore(datastore).devaddr(),amount.sub(amount.mul(95).div(100)));
        }
        uint pending = amount.mul(accKSJPerShare).div(1e12).sub(rewardDebt);
        uint rewards = pending.add(viewDynamicReward(msg.sender));
        IKsjDataStore(datastore).updatePoolUsdt( _pid, amountU ,2);
        IKsjDataStore(datastore).safeSendKsj(msg.sender, rewards);
        IKsjDataStore(datastore).setDeposit( _pid, msg.sender,_dtimes, 0,0,2) ;
        IKsjDataStore(datastore).updateUser( msg.sender,address(0),0,IKsjDataStore(datastore).dynamicPerShare(), amountU,amount,2) ;
        IKsjDataStore(datastore).updateUserTotal(msg.sender,pending,viewDynamicReward(msg.sender));
        
        updateActDyAmount( pending,msg.sender,_pid,accKSJPerShare);
        
        
        (,address invitor, uint level,,,,,,,,) = IKsjDataStore(datastore).userInfo(msg.sender);
        excuteMore(_pid, invitor, 1, amount, rewards,0,level,2);
        emit Withdraw(msg.sender, _pid, amount);
    }
    
    function viewUsdtAvailable(address _pair,uint _lp) public view returns(uint){
        uint totalSupply = IUniswapPair(_pair).totalSupply();
        address token00 = IUniswapPair(_pair).token0();
        address token01 = IUniswapPair(_pair).token1();
        uint amount0 = _lp.mul(IERC20(token00).balanceOf(_pair)) / totalSupply; 
        uint amount1 = _lp.mul(IERC20(token01).balanceOf(_pair)) / totalSupply; 
        return token00 == usdtAddr ? amount0 : amount1;
        // return _lp;
    }
    function viewUstdToLpAvailable(address _pair,uint _usdtAm) public view returns(uint){
        uint totalSupply = IUniswapPair(_pair).totalSupply();
        address token00 = IUniswapPair(_pair).token0();
        address token01 = IUniswapPair(_pair).token1();
        uint amount0 = _usdtAm.mul(totalSupply).div(IERC20(token00).balanceOf(_pair));
        uint amount1 = _usdtAm.mul(totalSupply).div(IERC20(token01).balanceOf(_pair));
        
        return token00 == usdtAddr ? amount0 : amount1;
        // return _lp;
    }

    //查询还剩余额度
    function remainingLimit(uint _pid,uint _inputAm) public view returns(uint _lpAm,uint _usdtAm ) {
        (address lpToken, ,,,,
        uint limitUsdt,
        uint curUsdtVal) = IKsjDataStore(datastore).poolInfo( _pid) ;
        uint willT =  curUsdtVal.add(viewUsdtAvailable(lpToken,_inputAm));
        if(willT > limitUsdt){
            uint uAm =  limitUsdt.sub(curUsdtVal);
            uint _lp = viewUstdToLpAvailable(lpToken,uAm);
            return (_lp,uAm);
        }else{
            return (_inputAm, viewUsdtAvailable(lpToken,_inputAm));
        }
        
    }

    function calLevel(uint _pid,uint _teamLp) public view returns(uint){
        (address lpToken, ,,,,,) = IKsjDataStore(datastore).poolInfo( _pid) ;
        uint _teamLpUsdt = viewUsdtAvailable(lpToken,_teamLp);
        if(_teamLpUsdt >= oneUsdt.mul(810_000)){
            return 4;
        }else if(_teamLpUsdt >= oneUsdt.mul(270_000)){
            return 3;
        }else if(_teamLpUsdt >= oneUsdt.mul(90_000)){
            return 2;
        }else if(_teamLpUsdt >= oneUsdt.mul(30_000)){
            return 1;
        }else {
            return uint(0);
        }
    }

    function emergencyWithdraw(uint256 _pid,uint _dtimes) public {
        require(isFlag);
        (address lpToken, ,,, ,,) = IKsjDataStore(datastore).poolInfo(_pid);
        ( uint256 amount, , ,uint endTime,) = IKsjDataStore(datastore).depositInfo(_pid,msg.sender,_dtimes);
        if(block.timestamp >= endTime){
            IKsjDataStore(datastore).safeSendLp(lpToken,msg.sender,amount);
        }else{
            IKsjDataStore(datastore).safeSendLp(lpToken,msg.sender,amount.mul(95).div(100));
            IKsjDataStore(datastore).safeSendLp(lpToken,IKsjDataStore(datastore).devaddr(),amount.sub(amount.mul(95).div(100)));
        }
        emit EmergencyWithdraw(msg.sender, _pid, amount);
        IKsjDataStore(datastore).setDeposit( _pid, msg.sender,_dtimes,amount,0 ,2);
    }
    
}

interface IKsjDataStore{
    function userInfo(address _user) external view returns(
        uint regitsTime,
        address invitor,
        uint level,
        uint teamLp,
        uint dynamicAmount,        
        uint rewardDebt,
        uint totalInvest,
        uint curId,
        uint totalStaticWithdraw,
        uint totalDynamicWithdraw,
        uint totalInvestUsdt
        );
    function poolInfo(uint _pid) external view returns(
        address lpToken,           // Address of LP token contract.
        uint256 allocPoint,       // How many allocation points assigned to this pool. ksjs to distribute per block.
        uint256 lastRewardTime,  // Last block number that ksjs distribution occurs.
        uint256 accKSJPerShare, // Accumulated ksjs per share, times 1e12. See below.
        uint daysLimit,
        uint limitUsdt,
        uint curUsdtVal);
    function depositInfo(uint _pid,address _user,uint _dtime) external view returns(
        uint256 amount,     // How many LP tokens the user has provided.
        uint256 rewardDebt, // Reward debt. See explanation below.
        uint startTime,
        uint endTime,
        uint amountU
    );
    function getInvitor(address) external view returns(address);
    function updateUser(address _user,address _invitor,uint _dyAm,uint _dynamicPerShare, uint _amountU,uint _lp,uint _indexId) external;
    function updateUserTotal(address _user, uint _reward,uint _dyReward) external;
    function setPool(uint _pid,uint _reward) external;
    function updatePoolUsdt(uint _pid,uint _amount ,uint _indexId) external;
    function setDeposit(uint _pid,address _user,uint _dtime,uint _amount,uint _amountU ,uint _indexId) external;
    function updateDepositDebt(uint _pid,address _user,uint _dtime) external;
    function updateTeamLp(uint,address _user, uint _lp,uint _indexId) external;
    function safeSendLp(address,address,uint) external;
    function safeSendKsj(address,uint) external;
    function getDepositAmount(uint,address,uint) external view returns(uint,uint);
    function devaddr() external view returns(address);
    function dynamicPerShare() external view returns(uint);
    function levelRate(uint) external view returns(uint);
    function viewDepositPidCount(uint,address) external view returns(uint);
    function depositPidCount(uint,address,uint) external view returns(uint);
    function totalAllocPoint() external view returns(uint);
    function sysAddr() external view returns(address);
}
interface IUniswapPair{
    function getReservers()external view  returns(uint,uint,uint);
    function totalSupply()external view returns(uint);
    function token0()external view returns(address);
    function token1()external view returns(address);
}


