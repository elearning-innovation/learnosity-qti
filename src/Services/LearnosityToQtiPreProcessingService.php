<?php

namespace LearnosityQti\Services;

use LearnosityQti\Exceptions\MappingException;
use LearnosityQti\Utils\MimeUtil;
use LearnosityQti\Utils\QtiMarshallerUtil;
use LearnosityQti\Utils\SimpleHtmlDom\SimpleHtmlDom;
use LearnosityQti\Utils\StringUtil;
use qtism\data\content\FlowCollection;
use qtism\data\content\xhtml\ObjectElement;
use qtism\data\content\xhtml\text\Div;
use LearnosityQti\Processors\QtiV2\Out\Constants as LearnosityExportConstant;

class LearnosityToQtiPreProcessingService
{
    private array $widgets;

    public function __construct(array $widgets = [])
    {
        $this->widgets = array_column($widgets, null, 'reference');
    }

    public function processJson(array $json): array
    {
        array_walk_recursive($json, function (&$item, $key) {
            if (is_string($item)) {
                // Replace nbsp with '&#160;'
                $item = str_replace('&nbsp;', '&#160;', $item);
                $item = $this->processHtml($item);
            }

            // Look for `template` attributes and make sure they're wrapped in a block element as QTI expects
            if ($key === 'template') {
                if (!str_starts_with($item, '<p>')) {
                    $item = '<div>' . $item . '</div>';
                }
            }
        });

        return $json;
    }

    private function processHtml($content)
    {
        $html = new SimpleHtmlDom();
        $html->load($content);

        // Replace <br> with <br />, <img ....> with <img />, etc
        /** @var array $selfClosingTags ie. `img, br, input, meta, link, hr, base, embed, spacer` */
        $selfClosingTags = implode(', ', array_keys($html->getSelfClosingTags()));

        foreach ($html->find($selfClosingTags) as $node) {
            if (!strpos($node->outertext, '/>')) {
                $node->outertext = rtrim($node->outertext, '>') . '/>';
            }
        }

        foreach ($html->find('img') as $node) {
            $src = $this->getQtiMediaSrcFromLearnositySrc($node->attr['src']);
            $node->outertext = str_replace($node->attr['src'], $src, $node->outertext);
        }

        // Replace these audioplayer and videoplayer feature with <object> nodes
        foreach ($html->find('span.learnosity-feature') as $node) {
            try {
                // Replace <span..> with <object..>
                $replacement = $this->getFeatureReplacementString($node);
                $node->outertext = $replacement;
            } catch (MappingException $e) {
                LogService::log(
                    $e->getMessage()
                    . '. Ignoring mapping feature '
                    . $node->outertext
                    . '`'
                );
            }
        }

        return $html->save();
    }

    /**
     * @throws MappingException
     */
    private function getFeatureReplacementString($node): bool|int|string
    {
        // Process inline feature
        if (isset($node->attr['data-type']) && isset($node->attr['data-src'])) {
            $src = trim($node->attr['data-src']);
            $type = trim($node->attr['data-type']);
            if ($type === 'audioplayer' || $type === 'videoplayer') {
                $src = $this->getQtiMediaSrcFromLearnositySrc($src);
                return QtiMarshallerUtil::marshallValidQti(
                    new ObjectElement($src, MimeUtil::guessMimeType(basename($src)))
                );
            }
        // Process regular question feature
        } else {
            $nodeClassAttribute = $node->attr['class'];
            $featureReference = $this->getFeatureReferenceFromClassName($nodeClassAttribute);
            if (isset($this->widgets[$featureReference])) {
                $feature = $this->widgets[$featureReference];
                $type = $feature['data']['type'] ?? '';
            } else {
                $feature = $this->widgets;
                $type = $feature[1]['type'] ?? '';
            }
            if ($type === 'audioplayer' || $type === 'videoplayer') {
                return 0;
            } elseif ($type === 'sharedpassage') {
                $flowCollection = new FlowCollection();
                $div = $this->createDivForSharedPassage();
                $object = new ObjectElement('sharedpassage/' . $featureReference . '.html', 'text/html');
                $object->setLabel($featureReference);
                $flowCollection->attach($object);
                $div->setContent($flowCollection);
                return QtiMarshallerUtil::marshallValidQti($div);
            } else {
                throw new MappingException($type . 'feature not supported');
            }
        }
        throw new MappingException($type . ' not supported');
    }

    private function createDivForSharedPassage(): Div
    {
        $div = new Div();
        $div->setClass(LearnosityExportConstant::SHARED_PASSAGE_DIV_CLASS);
        return $div;
    }

    private function getFeatureReferenceFromClassName($classname): array|string|null
    {
        // Parse classname, ie `learnosity-feature feature-DEMOFEATURE123`
        // Then, return `DEMOFEATURE123`
        $parts = preg_split('/\s+/', $classname);
        foreach ($parts as $part) {
            if (StringUtil::startsWith(strtolower($part), 'feature-')) {
                return str_replace('feature-', '', $parts[1]);
            }
        }
        // TODO: throw exception
        return null;
    }

    /**
     * This method take the original media source and return the desired media path
     * for an item based on their media type.
     *
     * @param string $src source of the desired media
     *
     * @return string media href
     */
    private function getQtiMediaSrcFromLearnositySrc(string $src): string
    {
        $fileName = substr($src, strlen(LearnosityExportConstant::DIRPATH_ASSETS));
        $mimeType = MimeUtil::guessMimeType($fileName);
        $mediaFormatArray = explode('/', $mimeType);
        $href = '';
        if (is_array($mediaFormatArray) && !empty($mediaFormatArray[0])) {
            $mediaFormat = $mediaFormatArray[0];
            if ($mediaFormat == 'video') {
                $href = '../' . LearnosityExportConstant::DIRNAME_VIDEO . '/' . $fileName;
            } elseif ($mediaFormat == 'audio') {
                $href = '../' . LearnosityExportConstant::DIRNAME_AUDIO . '/' . $fileName;
            } elseif ($mediaFormat == 'image') {
                $href = '../' . LearnosityExportConstant::DIRNAME_IMAGES . '/' . $fileName;
            }
        }
        return $href;
    }
}
