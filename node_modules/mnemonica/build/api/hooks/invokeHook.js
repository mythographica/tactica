'use strict';
Object.defineProperty(exports, "__esModule", { value: true });
exports.invokeHook = void 0;
const flowCheckers_1 = require("./flowCheckers");
const hop_1 = require("../../utils/hop");
const invokeHook = function (hookType, opts) {
    const { type, existentInstance, inheritedInstance, args, creator } = opts;
    const invocationResults = new Set();
    const self = this;
    if ((0, hop_1.hop)(self.hooks, hookType)) {
        const { TypeName, } = type;
        const hookArgs = {
            type,
            TypeName,
            existentInstance,
            args,
        };
        if (typeof inheritedInstance === 'object') {
            Object.assign(hookArgs, {
                inheritedInstance,
                throwModificationError(error) {
                    creator.throwModificationError(error);
                }
            });
        }
        this.hooks[hookType].forEach((hook) => {
            const result = hook.call(self, hookArgs);
            invocationResults.add(result);
        });
        const flowChecker = flowCheckers_1.flowCheckers.get(this);
        if (typeof flowChecker === 'function') {
            flowChecker
                .call(this, Object.assign({}, {
                invocationResults,
                hookType,
            }, hookArgs));
        }
    }
    return invocationResults;
};
exports.invokeHook = invokeHook;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiaW52b2tlSG9vay5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbIi4uLy4uLy4uL3NyYy9hcGkvaG9va3MvaW52b2tlSG9vay50cyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQSxZQUFZLENBQUM7OztBQUViLGlEQUE4QztBQUU5Qyx5Q0FBc0M7QUFFL0IsTUFBTSxVQUFVLEdBQUcsVUFBc0IsUUFBZ0IsRUFBRSxJQUFnQztJQUVqRyxNQUFNLEVBQ0wsSUFBSSxFQUNKLGdCQUFnQixFQUNoQixpQkFBaUIsRUFDakIsSUFBSSxFQUVKLE9BQU8sRUFDUCxHQUFHLElBQUksQ0FBQztJQUVULE1BQU0saUJBQWlCLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztJQUdwQyxNQUFNLElBQUksR0FBRyxJQUFJLENBQUM7SUFFbEIsSUFBSyxJQUFBLFNBQUcsRUFBRSxJQUFJLENBQUMsS0FBSyxFQUFFLFFBQVEsQ0FBRSxFQUFHLENBQUM7UUFLbkMsTUFBTSxFQUNMLFFBQVEsR0FFUixHQUFHLElBQUksQ0FBQztRQUVULE1BQU0sUUFBUSxHQUFHO1lBQ2hCLElBQUk7WUFDSixRQUFRO1lBQ1IsZ0JBQWdCO1lBQ2hCLElBQUk7U0FDSixDQUFDO1FBRUYsSUFBSyxPQUFPLGlCQUFpQixLQUFLLFFBQVEsRUFBRyxDQUFDO1lBQzdDLE1BQU0sQ0FBQyxNQUFNLENBQUUsUUFBUSxFQUFFO2dCQUN4QixpQkFBaUI7Z0JBQ2pCLHNCQUFzQixDQUFHLEtBQVk7b0JBQ3BDLE9BQU8sQ0FBQyxzQkFBc0IsQ0FBRSxLQUFLLENBQUUsQ0FBQztnQkFDekMsQ0FBQzthQUNELENBQUUsQ0FBQztRQUNMLENBQUM7UUFHRCxJQUFJLENBQUMsS0FBSyxDQUFFLFFBQVEsQ0FBRSxDQUFDLE9BQU8sQ0FBRSxDQUFFLElBQTRELEVBQUcsRUFBRTtZQUNsRyxNQUFNLE1BQU0sR0FBRyxJQUFJLENBQUMsSUFBSSxDQUFFLElBQUksRUFBRSxRQUFRLENBQUUsQ0FBQztZQUMzQyxpQkFBaUIsQ0FBQyxHQUFHLENBQUUsTUFBTSxDQUFFLENBQUM7UUFDakMsQ0FBQyxDQUFFLENBQUM7UUFFSixNQUFNLFdBQVcsR0FBRywyQkFBWSxDQUFDLEdBQUcsQ0FBRSxJQUFJLENBQUUsQ0FBQztRQUM3QyxJQUFLLE9BQU8sV0FBVyxLQUFLLFVBQVUsRUFBRyxDQUFDO1lBQ3pDLFdBQVc7aUJBQ1QsSUFBSSxDQUFFLElBQUksRUFBRSxNQUFNLENBQUMsTUFBTSxDQUFFLEVBQUUsRUFBRTtnQkFDL0IsaUJBQWlCO2dCQUNqQixRQUFRO2FBQ1IsRUFBRSxRQUFRLENBQUUsQ0FBRSxDQUFDO1FBQ2xCLENBQUM7SUFFRixDQUFDO0lBRUQsT0FBTyxpQkFBaUIsQ0FBQztBQUUxQixDQUFDLENBQUM7QUE3RFcsUUFBQSxVQUFVLGNBNkRyQiIsInNvdXJjZXNDb250ZW50IjpbIid1c2Ugc3RyaWN0JztcblxuaW1wb3J0IHsgZmxvd0NoZWNrZXJzIH0gZnJvbSAnLi9mbG93Q2hlY2tlcnMnO1xuXG5pbXBvcnQgeyBob3AgfSBmcm9tICcuLi8uLi91dGlscy9ob3AnO1xuXG5leHBvcnQgY29uc3QgaW52b2tlSG9vayA9IGZ1bmN0aW9uICggdGhpczogYW55LCBob29rVHlwZTogc3RyaW5nLCBvcHRzOiB7IFsgaW5kZXg6IHN0cmluZyBdOiBhbnkgfSApIHtcblxuXHRjb25zdCB7XG5cdFx0dHlwZSxcblx0XHRleGlzdGVudEluc3RhbmNlLFxuXHRcdGluaGVyaXRlZEluc3RhbmNlLFxuXHRcdGFyZ3MsXG5cdFx0Ly8gSW5zdGFuY2VNb2RpZmljYXRvcixcblx0XHRjcmVhdG9yXG5cdH0gPSBvcHRzO1xuXG5cdGNvbnN0IGludm9jYXRpb25SZXN1bHRzID0gbmV3IFNldCgpO1xuXG5cdC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tdGhpcy1hbGlhc1xuXHRjb25zdCBzZWxmID0gdGhpcztcblxuXHRpZiAoIGhvcCggc2VsZi5ob29rcywgaG9va1R5cGUgKSApIHtcblxuXHRcdC8vIFwidGhpc1wiIHJlZmVyZXMgdG9cblx0XHQvLyB0eXBlLCBpZiBjYWxsZWQgZnJvbSB0eXBlc1xuXG5cdFx0Y29uc3Qge1xuXHRcdFx0VHlwZU5hbWUsXG5cdFx0XHQvLyBwYXJlbnRUeXBlLFxuXHRcdH0gPSB0eXBlO1xuXG5cdFx0Y29uc3QgaG9va0FyZ3MgPSB7XG5cdFx0XHR0eXBlLFxuXHRcdFx0VHlwZU5hbWUsXG5cdFx0XHRleGlzdGVudEluc3RhbmNlLFxuXHRcdFx0YXJncyxcblx0XHR9O1xuXG5cdFx0aWYgKCB0eXBlb2YgaW5oZXJpdGVkSW5zdGFuY2UgPT09ICdvYmplY3QnICkge1xuXHRcdFx0T2JqZWN0LmFzc2lnbiggaG9va0FyZ3MsIHtcblx0XHRcdFx0aW5oZXJpdGVkSW5zdGFuY2UsXG5cdFx0XHRcdHRocm93TW9kaWZpY2F0aW9uRXJyb3IgKCBlcnJvcjogRXJyb3IgKSB7XG5cdFx0XHRcdFx0Y3JlYXRvci50aHJvd01vZGlmaWNhdGlvbkVycm9yKCBlcnJvciApO1xuXHRcdFx0XHR9XG5cdFx0XHR9ICk7XG5cdFx0fVxuXG5cdFx0IFxuXHRcdHRoaXMuaG9va3NbIGhvb2tUeXBlIF0uZm9yRWFjaCggKCBob29rOiAoIHRoaXM6IHVua25vd24sIGhvb2tQYXJhbXM6IHR5cGVvZiBob29rQXJncyApID0+IHZvaWQgKSA9PiB7XG5cdFx0XHRjb25zdCByZXN1bHQgPSBob29rLmNhbGwoIHNlbGYsIGhvb2tBcmdzICk7XG5cdFx0XHRpbnZvY2F0aW9uUmVzdWx0cy5hZGQoIHJlc3VsdCApO1xuXHRcdH0gKTtcblxuXHRcdGNvbnN0IGZsb3dDaGVja2VyID0gZmxvd0NoZWNrZXJzLmdldCggdGhpcyApO1xuXHRcdGlmICggdHlwZW9mIGZsb3dDaGVja2VyID09PSAnZnVuY3Rpb24nICkge1xuXHRcdFx0Zmxvd0NoZWNrZXJcblx0XHRcdFx0LmNhbGwoIHRoaXMsIE9iamVjdC5hc3NpZ24oIHt9LCB7XG5cdFx0XHRcdFx0aW52b2NhdGlvblJlc3VsdHMsXG5cdFx0XHRcdFx0aG9va1R5cGUsXG5cdFx0XHRcdH0sIGhvb2tBcmdzICkgKTtcblx0XHR9XG5cblx0fVxuXG5cdHJldHVybiBpbnZvY2F0aW9uUmVzdWx0cztcblxufTtcbiJdfQ==