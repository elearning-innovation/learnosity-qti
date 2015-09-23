<?php

namespace Learnosity\Entities\QuestionTypes;

use Learnosity\Entities\BaseQuestionTypeAttribute;

/**
 * This class is auto-generated based on Schemas API and you should not modify its content
 * Metadata: {"responses":"v2.72.0","feedback":"v2.71.0","features":"v2.72.0"}
 */
class association_validation_valid_response extends BaseQuestionTypeAttribute
{
    protected $score;
    protected $value;

    public function __construct()
    {
    }

    /**
     * Get Score \
     * Score for this valid response. \
     *
     * @return number $score \
     */
    public function get_score()
    {
        return $this->score;
    }

    /**
     * Set Score \
     * Score for this valid response. \
     *
     * @param number $score \
     */
    public function set_score($score)
    {
        $this->score = $score;
    }

    /**
     * Get value \
     * An array containing the valid responses for each item in the <em>stimulus_list</em> in corresponding order. \
     *
     * @return array $value \
     */
    public function get_value()
    {
        return $this->value;
    }

    /**
     * Set value \
     * An array containing the valid responses for each item in the <em>stimulus_list</em> in corresponding order. \
     *
     * @param array $value \
     */
    public function set_value(array $value)
    {
        $this->value = $value;
    }


}

