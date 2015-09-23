<?php

namespace Learnosity\Entities\QuestionTypes;

use Learnosity\Entities\BaseQuestionType;

/**
 * This class is auto-generated based on Schemas API and you should not modify its content
 * Metadata: {"responses":"v2.72.0","feedback":"v2.71.0","features":"v2.72.0"}
 */
class numberline extends BaseQuestionType
{
    protected $is_math;
    protected $metadata;
    protected $stimulus;
    protected $stimulus_review;
    protected $type;
    protected $ui_style;
    protected $feedback_attempts;
    protected $instant_feedback;
    protected $validation;
    protected $line;
    protected $ticks;
    protected $labels;
    protected $snap_to_ticks;
    protected $snap_vertically;
    protected $points;

    public function __construct(
        $type,
        array $points
    ) {
        $this->type   = $type;
        $this->points = $points;
    }

    /**
     * Get Has Mathematical Formulas \
     * Set to <strong>true</strong> to have LaTeX or MathML contents to be rendered with mathjax. \
     *
     * @return boolean $is_math \
     */
    public function get_is_math()
    {
        return $this->is_math;
    }

    /**
     * Set Has Mathematical Formulas \
     * Set to <strong>true</strong> to have LaTeX or MathML contents to be rendered with mathjax. \
     *
     * @param boolean $is_math \
     */
    public function set_is_math($is_math)
    {
        $this->is_math = $is_math;
    }

    /**
     * Get metadata \
     *  \
     *
     * @return numberline_metadata $metadata \
     */
    public function get_metadata()
    {
        return $this->metadata;
    }

    /**
     * Set metadata \
     *  \
     *
     * @param numberline_metadata $metadata \
     */
    public function set_metadata(numberline_metadata $metadata)
    {
        $this->metadata = $metadata;
    }

    /**
     * Get Stimulus \
     * <a data-toggle="modal" href="#supportedTags">HTML</a>/Text content displayed in all states (initial, resume, review) ren
     * dered <strong>above</strong> the response area. Supports embedded <a href="http://docs.learnosity.com/questionsapi/featu
     * retypes.php" target="_blank">Feature &lt;span&gt; tags</a>. \
     *
     * @return string $stimulus \
     */
    public function get_stimulus()
    {
        return $this->stimulus;
    }

    /**
     * Set Stimulus \
     * <a data-toggle="modal" href="#supportedTags">HTML</a>/Text content displayed in all states (initial, resume, review) ren
     * dered <strong>above</strong> the response area. Supports embedded <a href="http://docs.learnosity.com/questionsapi/featu
     * retypes.php" target="_blank">Feature &lt;span&gt; tags</a>. \
     *
     * @param string $stimulus \
     */
    public function set_stimulus($stimulus)
    {
        $this->stimulus = $stimulus;
    }

    /**
     * Get Stimulus in review \
     * <a data-toggle="modal" href="#supportedTags">HTML</a>/Text content displayed <strong>only</strong> in review state rende
     * red <strong>above</strong> the response area. Supports embedded <a href="http://docs.learnosity.com/questionsapi/feature
     * types.php" target="_blank">Feature &lt;span&gt; tags</a>. Will override stimulus in review state. \
     *
     * @return string $stimulus_review \
     */
    public function get_stimulus_review()
    {
        return $this->stimulus_review;
    }

    /**
     * Set Stimulus in review \
     * <a data-toggle="modal" href="#supportedTags">HTML</a>/Text content displayed <strong>only</strong> in review state rende
     * red <strong>above</strong> the response area. Supports embedded <a href="http://docs.learnosity.com/questionsapi/feature
     * types.php" target="_blank">Feature &lt;span&gt; tags</a>. Will override stimulus in review state. \
     *
     * @param string $stimulus_review \
     */
    public function set_stimulus_review($stimulus_review)
    {
        $this->stimulus_review = $stimulus_review;
    }

    /**
     * Get Question Type \
     *  \
     *
     * @return string $type \
     */
    public function get_type()
    {
        return $this->type;
    }

    /**
     * Set Question Type \
     *  \
     *
     * @param string $type \
     */
    public function set_type($type)
    {
        $this->type = $type;
    }

    /**
     * Get ui_style \
     *  \
     *
     * @return numberline_ui_style $ui_style \
     */
    public function get_ui_style()
    {
        return $this->ui_style;
    }

    /**
     * Set ui_style \
     *  \
     *
     * @param numberline_ui_style $ui_style \
     */
    public function set_ui_style(numberline_ui_style $ui_style)
    {
        $this->ui_style = $ui_style;
    }

    /**
     * Get Number of feedback attempts allowed \
     * If instant_feedback is true, this field determines how many times the user can click on the 'Check Answer' button, with
     * 0 being unlimited. \
     *
     * @return number $feedback_attempts \
     */
    public function get_feedback_attempts()
    {
        return $this->feedback_attempts;
    }

    /**
     * Set Number of feedback attempts allowed \
     * If instant_feedback is true, this field determines how many times the user can click on the 'Check Answer' button, with
     * 0 being unlimited. \
     *
     * @param number $feedback_attempts \
     */
    public function set_feedback_attempts($feedback_attempts)
    {
        $this->feedback_attempts = $feedback_attempts;
    }

    /**
     * Get Provide instant feedback \
     * Flag to determine whether to display a 'Check Answer' button to provide instant feedback to the user. \
     *
     * @return boolean $instant_feedback \
     */
    public function get_instant_feedback()
    {
        return $this->instant_feedback;
    }

    /**
     * Set Provide instant feedback \
     * Flag to determine whether to display a 'Check Answer' button to provide instant feedback to the user. \
     *
     * @param boolean $instant_feedback \
     */
    public function set_instant_feedback($instant_feedback)
    {
        $this->instant_feedback = $instant_feedback;
    }

    /**
     * Get validation \
     * Validation object that includes options on how this question will be automarked \
     *
     * @return numberline_validation $validation \
     */
    public function get_validation()
    {
        return $this->validation;
    }

    /**
     * Set validation \
     * Validation object that includes options on how this question will be automarked \
     *
     * @param numberline_validation $validation \
     */
    public function set_validation(numberline_validation $validation)
    {
        $this->validation = $validation;
    }

    /**
     * Get Line \
     * Defines the number line \
     *
     * @return numberline_line $line \
     */
    public function get_line()
    {
        return $this->line;
    }

    /**
     * Set Line \
     * Defines the number line \
     *
     * @param numberline_line $line \
     */
    public function set_line(numberline_line $line)
    {
        $this->line = $line;
    }

    /**
     * Get Ticks \
     * Defines the Number line ticks \
     *
     * @return numberline_ticks $ticks \
     */
    public function get_ticks()
    {
        return $this->ticks;
    }

    /**
     * Set Ticks \
     * Defines the Number line ticks \
     *
     * @param numberline_ticks $ticks \
     */
    public function set_ticks(numberline_ticks $ticks)
    {
        $this->ticks = $ticks;
    }

    /**
     * Get Labels \
     * Defines the labels to draw on the number line \
     *
     * @return numberline_labels $labels \
     */
    public function get_labels()
    {
        return $this->labels;
    }

    /**
     * Set Labels \
     * Defines the labels to draw on the number line \
     *
     * @param numberline_labels $labels \
     */
    public function set_labels(numberline_labels $labels)
    {
        $this->labels = $labels;
    }

    /**
     * Get Snap to ticks \
     * Whether dragged points should snap to the ticks specified by ticks.distance and labels.points \
     *
     * @return boolean $snap_to_ticks \
     */
    public function get_snap_to_ticks()
    {
        return $this->snap_to_ticks;
    }

    /**
     * Set Snap to ticks \
     * Whether dragged points should snap to the ticks specified by ticks.distance and labels.points \
     *
     * @param boolean $snap_to_ticks \
     */
    public function set_snap_to_ticks($snap_to_ticks)
    {
        $this->snap_to_ticks = $snap_to_ticks;
    }

    /**
     * Get Snap vertically \
     * Whether dragged points should snap to the line when dropped above it \
     *
     * @return boolean $snap_vertically \
     */
    public function get_snap_vertically()
    {
        return $this->snap_vertically;
    }

    /**
     * Set Snap vertically \
     * Whether dragged points should snap to the line when dropped above it \
     *
     * @param boolean $snap_vertically \
     */
    public function set_snap_vertically($snap_vertically)
    {
        $this->snap_vertically = $snap_vertically;
    }

    /**
     * Get Points \
     * Array containing the points the user has to position on the number line. Possible formats are: text, number, fraction an
     * d mixed fraction. The field doesn't support LaTeX because of rendering complexity. \
     *
     * @return array $points \
     */
    public function get_points()
    {
        return $this->points;
    }

    /**
     * Set Points \
     * Array containing the points the user has to position on the number line. Possible formats are: text, number, fraction an
     * d mixed fraction. The field doesn't support LaTeX because of rendering complexity. \
     *
     * @param array $points \
     */
    public function set_points(array $points)
    {
        $this->points = $points;
    }


    public function get_widget_type()
    {
        return 'response';
    }
}

