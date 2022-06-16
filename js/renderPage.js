
import { getFontSize, calcWordWidth, calcWordMetrics } from "./textUtils.js"
import { updateHOCRBoundingBoxWord, updateHOCRWord } from "./interfaceEdit.js";
import { round3, rotateBoundingBox } from "./miscUtils.js"

const fontSizeElem = /** @type {HTMLInputElement} */(document.getElementById('fontSize'));
const wordFontElem = /** @type {HTMLInputElement} */(document.getElementById('wordFont'));
const autoRotateCheckboxElem = /** @type {HTMLInputElement} */(document.getElementById('autoRotateCheckbox'));
const rangeBaselineElem = /** @type {HTMLInputElement} */(document.getElementById('rangeBaseline'));
const showBoundingBoxesElem = /** @type {HTMLInputElement} */(document.getElementById('showBoundingBoxes'));


export async function renderPage(canvas, doc, xmlDoc, mode = "screen", defaultFont, lineMode = false, imgDims, canvasDims, angle, pdfMode, fontObj, leftAdjX) {

  let ctx = canvas.getContext('2d');

  let canvasWidth = canvasDims[1];
  let canvasHeight = canvasDims[0];

  const sinAngle = Math.sin(angle * (Math.PI / 180));
  const cosAngle = Math.cos(angle * (Math.PI / 180));

  const shiftX = sinAngle * (imgDims[0] * 0.5) * -1 || 0;
  const shiftY = sinAngle * ((imgDims[1] - shiftX) * 0.5) || 0;


  let lines = xmlDoc.getElementsByClassName("ocr_line");

  let fontSize;
  for (let i = 0; i < lines.length; i++) {
    let line = lines[i]
    let titleStrLine = line.getAttribute('title');

    let linebox = [...titleStrLine.matchAll(/bbox(?:es)?(\s+[\d\-]+)(\s+[\d\-]+)?(\s+[\d\-]+)?(\s+[\d\-]+)?/g)][0].slice(1, 5).map(function (x) { return parseInt(x); });
    let baseline = titleStrLine.match(/baseline(\s+[\d\.\-]+)(\s+[\d\.\-]+)/);
    if (baseline != null) {
      baseline = baseline.slice(1, 5).map(function (x) { return parseFloat(x); });
    } else {
      baseline = [0, 0];
    }
    let words = line.getElementsByClassName("ocrx_word");



    // If possible (native Tesseract HOCR) get font size using x-height.
    // If not possible (Abbyy XML) get font size using ascender height.
    let letterHeight = titleStrLine.match(/x_size\s+([\d\.\-]+)/);
    let ascHeight = titleStrLine.match(/x_ascenders\s+([\d\.\-]+)/);
    let descHeight = titleStrLine.match(/x_descenders\s+([\d\.\-]+)/);
    if (letterHeight != null && ascHeight != null && descHeight != null) {
      letterHeight = parseFloat(letterHeight[1]);
      ascHeight = parseFloat(ascHeight[1]);
      descHeight = parseFloat(descHeight[1]);
      let xHeight = letterHeight - ascHeight - descHeight;
      fontSize = getFontSize(defaultFont, xHeight, "o");
    } else if (letterHeight != null) {
      letterHeight = parseFloat(letterHeight[1]);
      descHeight = descHeight != null ? parseFloat(descHeight[1]) : 0;
      fontSize = getFontSize(defaultFont, letterHeight - descHeight, "A");
    }

    // If none of the above conditions are met (not enough info to calculate font size), the font size from the previous line is reused.
    ctx.font = 1000 + 'px ' + defaultFont;
    //const AMetrics = ctx.measureText("A");
    const oMetrics = ctx.measureText("o");
    //const jMetrics = ctx.measureText("gjpqy");
    ctx.font = fontSize + 'px ' + defaultFont;

    const colorModeElem = /** @type {HTMLInputElement} */(document.getElementById('colorMode'));
    let angleAdjXLine = 0;
    let angleAdjYLine = 0;
    if ((true) && Math.abs(angle ?? 0) > 0.05) {

      const angleAdjXInt = sinAngle * (linebox[3] + baseline[1]);
      const angleAdjYInt = sinAngle * (linebox[0] + angleAdjXInt / 2) * -1;

      angleAdjXLine = angleAdjXInt + shiftX;
      angleAdjYLine = angleAdjYInt + shiftY;

    }

    for (let j = 0; j < words.length; j++) {
      let word = words[j];

      let titleStr = word.getAttribute('title') ?? "";
      let styleStr = word.getAttribute('style') ?? "";

      const compCount = word.getAttribute('compCount') ?? "";
      const compStatus = word.getAttribute('compStatus') ?? "";
      //const matchTruth = compCount == "1" && compStatus == "1";
      const matchTruth = compStatus == "1";
      const fillColorHexMatch = matchTruth ? "#00ff7b" : "#ff0000";

      if (!word.childNodes[0]?.textContent.trim()) continue;

      let box = [...titleStr.matchAll(/bbox(?:es)?(\s+[\d\-]+)(\s+[\d\-]+)?(\s+[\d\-]+)?(\s+[\d\-]+)?/g)][0].slice(1, 5).map(function (x) { return parseInt(x); })
      let box_width = box[2] - box[0];
      let box_height = box[3] - box[1];

      const angleAdjXWord = Math.abs(angle) >= 1 ? angleAdjXLine + (1 - cosAngle) * (box[0] - linebox[0]) : angleAdjXLine;

      let wordText, wordSup, wordDropCap;
      if (/\<sup\>/i.test(word.innerHTML)) {
        wordText = word.innerHTML.replace(/^\s*\<sup\>/i, "");
        wordText = wordText.replace(/\<\/sup\>\s*$/i, "");
        wordSup = true;
        wordDropCap = false;
      } else if (/\<span class\=[\'\"]ocr_dropcap[\'\"]\>/i.test(word.innerHTML)) {
        wordText = word.innerHTML.replace(/^\s*<span class\=[\'\"]ocr_dropcap[\'\"]\>/i, "");
        wordText = wordText.replace(/\<\/span\>\s*$/i, "");
        wordSup = false;
        wordDropCap = true;
      } else {
        wordText = word.childNodes[0].nodeValue;
        wordSup = false;
        wordDropCap = false;
      }

      let wordFontSize;
      let fontSizeStr = styleStr.match(/font\-size\:\s*(\d+)/i);
      if (fontSizeStr != null) {
        wordFontSize = parseFloat(fontSizeStr[1]);
      } else if (wordSup) {
        // All superscripts are assumed to be numbers for now
        wordFontSize = getFontSize(defaultFont, box_height, "1", ctx);
      } else if (wordDropCap) {
        // Note: In addition to being taller, drop caps are often narrower than other glyphs.
        // Unfortunately, while Fabric JS (canvas library) currently supports horizontally scaling glyphs,
        // pdfkit (pdf library) does not.  This feature should be added to Scribe if pdfkit supports it
        // in the future.
        // https://github.com/foliojs/pdfkit/issues/1032
        wordFontSize = getFontSize(defaultFont, box_height, wordText.slice(0, 1), ctx);
      } else {
        wordFontSize = fontSize;
      }

      let fontStyle;
      if (/italic/i.test(styleStr)) {
        fontStyle = "italic";
      } else if (/small\-caps/i.test(styleStr)) {
        fontStyle = "small-caps";
      } else {
        fontStyle = "normal";
      }


      let fontFamilyWord = styleStr.match(/font\-family\s{0,3}\:\s{0,3}[\'\"]?([^\'\";]+)/);
      let defaultFontFamily;
      if (fontFamilyWord == null) {
        fontFamilyWord = defaultFont
        defaultFontFamily = true;
      } else {
        fontFamilyWord = fontFamilyWord[1].trim();
        defaultFontFamily = false;
      }


      let x_wconf;
      let confMatch = titleStr.match(/(?:;|\s)x_wconf\s+(\d+)/);
      let wordConf = 0;
      if (confMatch != null) {
        wordConf = parseInt(confMatch[1]);
      }

      let word_id = word.getAttribute('id');


      const confThreshHigh = 85;
      const confThreshMed =  75;

      let fillColorHex;
      if (wordConf > confThreshHigh) {
        // fillColorRGB = "rgb(0,255,125)"
        fillColorHex = "#00ff7b";
      } else if (wordConf > confThreshMed) {
        // fillColorRGB = "rgb(255,200,0)"
        fillColorHex = "#ffc800";
      } else {
        // fillColorRGB = "rgb(255,0,0)"
        fillColorHex = "#ff0000";
      }

      let missingKerning, kerning;
      //let kerning;
      let kerningMatch = styleStr.match(/letter-spacing\:([\d\.\-]+)/);
      if (kerningMatch == null) {
        kerning = 0;
        missingKerning = true;
      } else {
        kerning = parseFloat(kerningMatch[1]);
        missingKerning = false;
      }

      const displayMode = "proof";

      let opacity_arg, fill_arg;
      // Set current text color and opacity based on display mode selected
      if (displayMode == "invis") {
        opacity_arg = 0
        fill_arg = "black"
      } else if (displayMode == "ebook") {
        opacity_arg = 1
        fill_arg = "black"
      } else if (displayMode == "eval") {
        opacity_arg = 1;
        fill_arg = fillColorHexMatch;
      } else {
        opacity_arg = 1
        fill_arg = fillColorHex
      }

      if (fontStyle == "small-caps") {
        ctx.font = wordFontSize + 'px ' + fontFamilyWord + " Small Caps";
      } else {
        ctx.font = fontStyle + " " + wordFontSize + 'px ' + fontFamilyWord;
      }

      const fontObjI = await fontObj[fontFamilyWord][fontStyle];

      // Calculate font glyph metrics for precise positioning
      let wordLastGlyphMetrics = fontObjI.charToGlyph(wordText.substr(-1)).getMetrics();
      let wordFirstGlyphMetrics = fontObjI.charToGlyph(wordText.substr(0, 1)).getMetrics();

      let wordLeftBearing = wordFirstGlyphMetrics.xMin * (fontSize / fontObjI.unitsPerEm);
      let wordRightBearing = wordLastGlyphMetrics.rightSideBearing * (fontSize / fontObjI.unitsPerEm);


      let wordWidth1 = ctx.measureText(wordText).width;
      let wordWidth = wordWidth1 - wordRightBearing - wordLeftBearing + (wordText.length - 1) * kerning;

      if(/Davenport/.test(wordText)){
        debugger;
      }


      //wordWidth = textbox.width
      // If kerning is off, change the kerning value for both the canvas textbox and HOCR
      if (wordText.length > 1 && Math.abs(box_width - wordWidth) > 1) {
        kerning = round3(kerning + (box_width - wordWidth) / (wordText.length - 1));
        if (missingKerning) {
          if (styleStr.length > 0) {
            styleStr = styleStr + ";";
          }
          styleStr = styleStr + "letter-spacing:" + kerning + "px";
        } else {
          styleStr = styleStr.replace(/(letter-spacing\:)([\d\.\-]+)/, "$1" + kerning);
        }
        word.setAttribute("style", styleStr);
      }

      globalThis.doc.font(fontFamilyWord + "-" + fontStyle);


      let top;
      if (wordSup || wordDropCap) {

        let angleAdjYSup = sinAngle * (box[0] - linebox[0]) * -1;

        if (wordSup) {
          top = linebox[3] + baseline[1] + angleAdjYLine + (box[3] - (linebox[3] + baseline[1])) + angleAdjYSup;
        } else {
          top = box[3] + angleAdjYLine + angleAdjYSup;
        }
      } else {
        top = linebox[3] + baseline[1] + angleAdjYLine;
      }
      let left = box[0] - wordLeftBearing + angleAdjXWord + leftAdjX;


      // Characters that go off the edge will cause an additional case to be made.
      // To avoid this, such characters are skipped.
      if (top <= 0 || top + wordFontSize >= canvasHeight || left <= 0 || left + wordWidth >= canvasWidth) {
        console.log("Skipping word: " + wordText);
        continue;
      }

      globalThis.doc.fontSize(wordFontSize);
      globalThis.doc.fillColor(fill_arg).fillOpacity(opacity_arg);

      globalThis.doc.text(
        wordText,
        left,
        top,
        {
          baseline: "alphabetic",
          characterSpacing: kerning
        })

    }
  }
}