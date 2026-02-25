'use strict';
Object.defineProperty(exports, "__esModule", { value: true });
exports.decorate = void 0;
exports.define = define;
exports.create = create;
/**
 * Tactica wrapper for mnemonica's define() and decorate()
 *
 * These wrappers provide automatic type inference without manual casting.
 * They preserve all mnemonica functionality while adding seamless TypeScript support.
 */
const mnemonica_1 = require("mnemonica");
Object.defineProperty(exports, "decorate", { enumerable: true, get: function () { return mnemonica_1.decorate; } });
/**
 * Wrapped define function that provides automatic type inference
 *
 * Usage:
 * ```typescript
 * import { define } from '@mnemonica/tactica';
 *
 * const UserType = define('UserType', function (this: UserTypeInstance) {
 *     this.name = '';
 * });
 *
 * // No casting needed!
 * const user = new UserType(); // user is typed as UserTypeInstance
 * const admin = new user.AdminType(); // admin is typed as AdminTypeInstance
 * ```
 */
function define(TypeName, constructor, config) {
    // Call mnemonica's define with proper type casting
    const TypeConstructor = (0, mnemonica_1.define)(TypeName, constructor, config);
    // Return the constructor with proper type inference
    return TypeConstructor;
}
/**
 * Creates an instance from a decorated class with proper type inference
 *
 * This helper function eliminates the need for manual type casting when
 * using mnemonica's @decorate() decorator on classes.
 *
 * Usage:
 * ```typescript
 * import { decorate, create } from '@mnemonica/tactica';
 *
 * // Define your class with @decorate()
 * @decorate()
 * class Order {
 *     orderId: string = '';
 *     total: number = 0;
 * }
 *
 * // Use create() instead of new - no casting needed!
 * const order = create<OrderInstance>(Order); // order is typed as OrderInstance
 * ```
 *
 * For nested/augmented types:
 * ```typescript
 * @decorate(Order)
 * class AugmentedOrder {
 *     addition: string = 'extra';
 * }
 *
 * const order = create<OrderInstance>(Order); // OrderInstance
 * const augmented = create<AugmentedOrderInstance>(AugmentedOrder); // AugmentedOrderInstance
 *
 * // Or create from instance
 * const augFromOrder = new order.AugmentedOrder(); // Still works!
 * ```
 */
function create(
// eslint-disable-next-line @typescript-eslint/no-explicit-any
Constructor) {
    return new Constructor();
}
//# sourceMappingURL=define.js.map