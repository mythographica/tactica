import { UsePipes, UseGuards, Body } from '@nestjs/common';
import { mvp } from '@mnemonica/nestjs';

export class CrateDto {
	mark = '';
}

export class GadgetGuard {
	canActivate () {
		return true;
	}
}

export class TokenDto {
	hue = '';
}

export class CrateController {
	@UsePipes(mvp.forType(CrateDto))
	createCrate (data: unknown) {
		return data;
	}

	@UseGuards(mvp.bindGuard('gadgets:write', GadgetGuard))
	replaceGadget () {
		return true;
	}

	mintToken (@Body(mvp.forType(TokenDto)) data: unknown) {
		return data;
	}
}
