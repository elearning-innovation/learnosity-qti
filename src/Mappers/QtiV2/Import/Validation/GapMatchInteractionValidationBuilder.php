<?php

namespace Learnosity\Mappers\QtiV2\Import\Validation;

class GapMatchInteractionValidationBuilder extends BaseGapMatchInteractionValidationBuilder
{
    function getValidationClassName()
    {
        return 'clozeassociation';
    }
}