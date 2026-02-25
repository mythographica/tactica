'use strict';

/**
 * Tactica wrapper for mnemonica's define() and decorate()
 *
 * These wrappers provide automatic type inference without manual casting.
 * They preserve all mnemonica functionality while adding seamless TypeScript support.
 */

import { define as mnemonicaDefine, decorate as mnemonicaDecorate } from 'mnemonica';

/**
 * Type helper for extracting instance type from constructor
 */
type InstanceType<T> = T extends { new (...args: any[]): infer R } ? R : never;

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
export function define<T>(
	TypeName: string,
	constructor: (this: T, ...args: any[]) => void,
	config?: object
): {
	new (...args: any[]): T;
	define: typeof define;
} & {
	[K in keyof T as T[K] extends { new (...args: any[]): any } ? K : never]: T[K];
} {
	// Call mnemonica's define with proper type casting
	const TypeConstructor = mnemonicaDefine(TypeName, constructor, config);

	// Return the constructor with proper type inference
	return TypeConstructor as any;
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
export function create<TInstance>(
	// eslint-disable-next-line @typescript-eslint/no-explicit-any
	Constructor: new (...args: any[]) => any
): TInstance {
	return new Constructor() as TInstance;
}

/**
 * Re-export mnemonica's decorate for use as decorator
 *
 * Note: Due to TypeScript limitations, @decorate() on classes cannot change
 * the return type of `new Class()`. Use the create() helper to get proper types:
 *
 * ```typescript
 * @decorate()
 * class Order { }
 *
 * // Instead of: new Order() as OrderInstance
 * const order = create(Order); // Properly typed as OrderInstance
 * ```
 */
export { mnemonicaDecorate as decorate };

/**
 * Utility type for getting instance type from a constructor
 */
export type { InstanceType };
