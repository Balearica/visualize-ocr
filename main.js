// File summary:
// Main file that defines all interface event listners, defines all global variables,
// and contains key functions for importing data and rendering to pdf/canvas.
//
// TODO: This file contains many miscellaneous functions and would benefit from being refactored.
// Additionally, various data stored as global variables

globalThis.d = function () {
  debugger;
}

import { renderText } from './js/exportRenderText.js';
import { renderHOCR } from './js/exportRenderHOCR.js';

import { renderPage } from './js/renderPage.js';

import { getFontSize, calcWordWidth, calcWordMetrics } from "./js/textUtils.js"

import { optimizeFont, calculateOverallFontMetrics } from "./js/fontOptimize.js";
import { loadFont, loadFontBrowser, loadFontFamily } from "./js/fontUtils.js";

import { getRandomAlphanum, quantile, sleep, readOcrFile, round3, rotateBoundingBox } from "./js/miscUtils.js";

import {
  deleteSelectedWords, toggleStyleSelectedWords, changeWordFontSize, toggleBoundingBoxesSelectedWords, changeWordFont, toggleSuperSelectedWords,
  updateHOCRWord, adjustBaseline, adjustBaselineRange, adjustBaselineRangeChange, updateHOCRBoundingBoxWord
} from "./js/interfaceEdit.js";

import { initMuPDFWorker } from "./mupdf/mupdf-async.js";


// Third party libraries
import { simd } from "./lib/wasm-feature-detect.js";
import Tesseract from './tess/tesseract.es6.js';

// Debugging functions
import { searchHOCR } from "./js/debug.js"

globalThis.searchHOCR = searchHOCR;

// Global variables containing fonts represented as OpenType.js objects and array buffers (respectively)
var leftGlobal;



// Object that keeps track of what type of input data is present
globalThis.inputDataModes = {
  // true if OCR data exists (whether from upload or built-in engine)
  xmlMode: undefined,
  // true if user uploaded pdf
  pdfMode: false,
  // true if user uploaded image files (.png, .jpeg)
  imageMode: false,
  // true if user re-uploaded HOCR data created by Scribe OCR
  resumeMode: false
}

// Object that keeps track of various global settings
globalThis.globalSettings = {
  simdSupport: false,
  defaultFont: "Libre Baskerville"
}

// Object for data currently being displayed on the canvas
globalThis.currentPage = {
  n: 0,
  backgroundImage: null,
  backgroundOpts: {},
  leftAdjX: 0,
  renderStatus: 0,
  xmlDoc: null
}


var parser = new DOMParser();

const uploaderElem = /** @type {HTMLInputElement} */(document.getElementById('uploader'));
uploaderElem.addEventListener('change', importFiles);

// Content that should be run once, after all dependencies are done loading are done loading
globalThis.runOnLoad = function () {

  // Load fonts
  loadFontFamily("Open Sans");
  loadFontFamily("Libre Baskerville");

}


// Define canvas
globalThis.canvas = new fabric.Canvas('c');
globalThis.ctx = canvas.getContext('2d');

// Resets the environment.
var fontMetricObjsMessage, loadCountHOCR;
async function clearFiles() {

  currentPage.n = 0;

  globalThis.imageAll = {};
  globalThis.hocrCurrent = [];
  globalThis.fontMetricsObj = {};
  globalThis.pageMetricsObj = {};
  fontMetricObjsMessage = [];

  if (globalThis.binaryScheduler) {
    const bs = await globalThis.binaryScheduler;
    bs.terminate();
    globalThis.binaryScheduler = null;
  }

  if (globalThis.muPDFScheduler) {
    const ms = await globalThis.muPDFScheduler;
    globalThis.ms.terminate();
    globalThis.muPDFScheduler = null;
  }

  loadCountHOCR = 0;

}

clearFiles();


async function importFiles() {

  globalThis.runOnLoad();

  const curFiles = uploaderElem.files;

  if (curFiles.length == 0) return;

  globalThis.pageMetricsObj["angleAll"] = new Array();
  globalThis.pageMetricsObj["dimsAll"] = new Array();
  globalThis.pageMetricsObj["leftAll"] = new Array();
  globalThis.pageMetricsObj["angleAdjAll"] = new Array();
  globalThis.pageMetricsObj["manAdjAll"] = new Array();


  // Sort files into (1) HOCR files, (2) image files, or (3) unsupported using extension.
  let imageFilesAll = new Array();
  let hocrFilesAll = new Array();
  let pdfFilesAll = new Array()
  let unsupportedFilesAll = new Array();
  let unsupportedExt = new Object;
  for (let i = 0; i < curFiles.length; i++) {
    const file = curFiles[i];
    let fileExt = file.name.match(/\.([^\.]+)$/)?.[1].toLowerCase() || "";

    if (["png", "jpeg", "jpg"].includes(fileExt)) {
      imageFilesAll.push(file);
      // All .gz files are assumed to be OCR data (xml) since all other file types can be compressed already
    } else if (["hocr", "xml", "html", "gz"].includes(fileExt)) {
      hocrFilesAll.push(file);
    } else if (["pdf"].includes(fileExt)) {
      pdfFilesAll.push(file);
    } else {
      unsupportedFilesAll.push(file);
      unsupportedExt[fileExt] = true;
    }
  }

  inputDataModes.pdfMode = pdfFilesAll.length == 1 ? true : false;
  inputDataModes.imageMode = imageFilesAll.length > 0 && !inputDataModes.pdfMode ? true : false;

  const xmlModeImport = hocrFilesAll.length > 0 ? true : false;

  imageFilesAll.sort((a, b) => (a.name > b.name) ? 1 : ((b.name > a.name) ? -1 : 0))
  hocrFilesAll.sort();

  // Set default download name
  globalThis.downloadFileName = pdfFilesAll.length > 0 ? pdfFilesAll[0].name : curFiles[0].name;
  globalThis.downloadFileName = globalThis.downloadFileName.replace(/\.\w{1,4}$/, "");
  globalThis.downloadFileName = globalThis.downloadFileName + ".pdf";

  // Check that input makes sense.  Valid options are:
  // (1) N HOCR files and 0 image files
  // (1) N HOCR files and N image files
  // (1) 1 HOCR file and N image files
  if (hocrFilesAll.length > 1 && inputDataModes.imageMode && hocrFilesAll.length != imageFilesAll.length) {
    throw new Error('Detected ' + hocrFilesAll.length + ' hocr files but ' + imageFilesAll.length + " image files.")
  }

  // In the case of 1 HOCR file
  const singleHOCRMode = hocrFilesAll.length == 1 ? true : false;

  //let pageCount, hocrCurrentRaw, abbyyMode;
  let hocrStrStart = "";
  let hocrStrEnd = "";
  let abbyyMode, hocrStrPages, hocrArrPages, pageCount, pageCountImage, pageCountHOCR;

  if (inputDataModes.pdfMode) {

    globalThis.pdfFile = pdfFilesAll[0];

    // Initialize scheduler
    await initSchedulerIfNeeded("muPDFScheduler");

    const ms = await globalThis.muPDFScheduler;

    pageCountImage = await ms.addJob('countPages', []);

    // If no XML data is provided, page sizes are calculated using muPDF alone
    if(!xmlModeImport) {
      // Confirm that 300 dpi leads to a reasonably sized image and lower dpi if not.
      const pageDims1 = (await ms.addJob('pageSizes', [300])).slice(1);

      // For reasons that are unclear, a small number of pages have been rendered into massive files
      // so a hard-cap on resolution must be imposed.
      const pageWidth1 = pageDims1.map((x) => x[0]);
      const pageDPI = pageWidth1.map((x) => Math.round(300 * 2000 / Math.max(x, 2000)));

      // In addition to capping the resolution, also switch the width/height
      const pageDims = pageDims1.map((x,i) => [Math.round(x[1]*pageDPI[i]/300),Math.round(x[0]*pageDPI[i]/300)]);

      globalThis.pageMetricsObj["dimsAll"] = pageDims;

    }

  } else if (inputDataModes.imageMode) {
    pageCountImage = imageFilesAll.length;
  }

  if (xmlModeImport) {

    if (singleHOCRMode) {
      const singleHOCRMode = true;
      let hocrStrAll = await readOcrFile(hocrFilesAll[0]);

      // Check whether input is Abbyy XML
      const node2 = hocrStrAll.match(/\>([^\>]+)/)[1];
      abbyyMode = /abbyy/i.test(node2) ? true : false;

      if (abbyyMode) {

        hocrStrPages = hocrStrAll.replace(/[\s\S]*?(?=\<page)/i, "");
        hocrArrPages = hocrStrPages.split(/(?=\<page)/);
      } else {

        // Check if re-imported from an earlier session (and therefore containing font metrics pre-calculated)
        inputDataModes.resumeMode = /\<meta name\=[\"\']font-metrics[\"\']/i.test(hocrStrAll);

        if (inputDataModes.resumeMode) {
          let fontMetricsStr = hocrStrAll.match(/\<meta name\=[\"\']font\-metrics[\"\'][^\<]+/i)[0];
          let contentStr = fontMetricsStr.match(/content\=[\"\']([\s\S]+?)(?=[\"\']\s{0,5}\/?\>)/i)[1].replace(/&quot;/g, '"');
          globalThis.fontMetricsObj = JSON.parse(contentStr);

        }

        hocrStrStart = hocrStrAll.match(/[\s\S]*?\<body\>/)[0];
        hocrStrEnd = hocrStrAll.match(/\<\/body\>[\s\S]*$/)[0];
        hocrStrPages = hocrStrAll.replace(/[\s\S]*?\<body\>/, "");
        hocrStrPages = hocrStrPages.replace(/\<\/body\>[\s\S]*$/, "");
        hocrStrPages = hocrStrPages.trim();

        hocrArrPages = hocrStrPages.split(/(?=\<div class\=[\'\"]ocr_page[\'\"])/);
      }

      pageCountHOCR = hocrArrPages.length;
      if (inputDataModes.imageMode && hocrArrPages.length != imageFilesAll.length) {
        throw new Error('Detected ' + hocrArrPages.length + ' pages in OCR but ' + imageFilesAll.length + " image files.")
      }
      globalThis.hocrCurrentRaw = Array(pageCountHOCR);
      for (let i = 0; i < pageCountHOCR; i++) {
        globalThis.hocrCurrentRaw[i] = hocrStrStart + hocrArrPages[i] + hocrStrEnd;
      }

    } else {
      const singleHOCRMode = false;
      pageCountHOCR = hocrFilesAll.length;

      // Check whether input is Abbyy XML using the first file
      let hocrStrFirst = await readOcrFile(hocrFilesAll[0]);
      const node2 = hocrStrFirst.match(/\>([^\>]+)/)[1];
      abbyyMode = /abbyy/i.test(node2) ? true : false;
    }

  }

  // If both OCR data and image data are present, confirm they have the same number of pages
  if (xmlModeImport && (inputDataModes.imageMode || inputDataModes.pdfMode)) {
    if (pageCountImage != pageCountHOCR) {
      document.getElementById("pageMismatchAlertText").textContent = " Page mismatch detected. Image data has " + pageCountImage + " pages while OCR data has " + pageCountHOCR + " pages."
      document.getElementById("pageMismatchAlert").setAttribute("style", "");
    }
  }

  pageCount = pageCountImage ?? pageCountHOCR;

  globalThis.hocrCurrent = Array(pageCount);
  globalThis.hocrCurrentRaw = globalThis.hocrCurrentRaw || Array(pageCount);

  // Global object that contains arrays with page images or related properties. 
  globalThis.imageAll = {
    // Unedited images uploaded by user (unused when user provides a PDF).
    nativeRaw: Array(pageCount),
    // Native images.  When the user uploads images directly, this contains whatever they uploaded.
    // When a user uploads a pdf, this will contain the images rendered by muPDF (either grayscale or color depending on setting).
    native: Array(pageCount),
    // Binarized image.
    binary: Array(pageCount),
    // Whether the native image was re-rendered with rotation applied. 
    nativeRotated: Array(pageCount),
    // Whether the binarized image was re-rendered with rotation applied. 
    binaryRotated: Array(pageCount),
    // [For pdf uploads only] Whether the "native" image was rendered in color or grayscale.
    nativeColor: Array(pageCount)
  }

  inputDataModes.xmlMode = new Array(pageCount);
  if (xmlModeImport) {
    inputDataModes.xmlMode.fill(true);
  } else {
    inputDataModes.xmlMode.fill(false);
  }

  let imageN = -1;
  let hocrN = -1;
  let firstImg = true;

  loadCountHOCR = 0;

  for (let i = 0; i < pageCount; i++) {

    // Note: As of Jan 22, exporting PDFs using BMP files is currently bugged in pdfKit (the colors channels can get switched)
    if (inputDataModes.imageMode) {

      const imageNi = imageN + 1;
      imageN = imageN + 1;

      const image = document.createElement('img');

      const reader = new FileReader();
      reader.addEventListener("load", () => {
        image.src = reader.result;

        globalThis.imageAll["nativeRaw"][imageNi] = image;
        globalThis.imageAll["native"][imageNi] = globalThis.imageAll["nativeRaw"][imageNi];

        updateDataProgress();

      }, false);

      reader.readAsDataURL(imageFilesAll[i]);

    }

    if (xmlModeImport) {
      // Process HOCR using web worker, reading from file first if that has not been done already
      if (singleHOCRMode) {
        //convertPageWorker.postMessage([globalThis.hocrCurrentRaw[i], i, abbyyMode]);
        convertPage([globalThis.hocrCurrentRaw[i], i, abbyyMode]).then(() => updateDataProgress());
      } else {
        const hocrFile = hocrFilesAll[i];
        const hocrNi = hocrN + 1;
        hocrN = hocrN + 1;
        //readOcrFile(hocrFile).then((x) => convertPageWorker.postMessage([x, hocrNi]));
        readOcrFile(hocrFile).then((x) => convertPage([x, i, undefined]).then(() => updateDataProgress()));
      }
    }

  }

}

async function initMuPDFScheduler(file, workers = 3) {
  globalThis.muPDFScheduler = await Tesseract.createScheduler();
  globalThis.muPDFScheduler["pngRenderCount"] = 0;
  for (let i = 0; i < workers; i++) {
    const w = await initMuPDFWorker();
    const fileData = await file.arrayBuffer();
    const pdfDoc = await w.openDocument(fileData, file.name);
    w["pdfDoc"] = pdfDoc;

    w.id = `png-${Math.random().toString(16).slice(3, 8)}`;
    globalThis.muPDFScheduler.addWorker(w);
  }
}

async function loadImage(url, elem) {
  return new Promise((resolve, reject) => {
    elem.onload = () => resolve(elem);
    elem.onerror = reject;
    elem.src = url;
  });
}


// Function that renders images and stores them in cache array (or returns early if the requested image already exists).
// This function contains 2 distinct image rendering steps:
// 1. Pages are rendered from .pdf to .png [either color or grayscale] using muPDF
// 1. Existing .png images are processed (currently rotation and/or thresholding) using Tesseract/Leptonica
async function renderPDFImageCache(pagesArr, rotate = null) {

  const colorMode = "gray";
  const colorName = colorMode == "binary" ? "binary" : "native";

  await Promise.allSettled(pagesArr.map((n) => {

    // In imageMode, if the current image is rotated but a non-rotated image is requested, revert to the original (user-uploaded) image. 
    if(inputDataModes.imageMode && rotate == false && globalThis.imageAll["nativeRotated"][n] == true) {
      // globalThis.imageAll["nativeColor"][n] = "color";
      globalThis.imageAll["nativeRotated"][n] = false;
      globalThis.imageAll["native"][n] = globalThis.imageAll["nativeRaw"][n];
    }

    // In pdfMode, determine whether an original/unedited version of the image needs to be obtained.
    // This can happen for 3 reasons:
    // 1. Page has not yet been rendered
    // 2. Page was previously rendered, but in different colorMode (gray vs. color)
    // 3. Page was overwritten by rotated version, but a non-rotated version is needed
    const renderNativePDF = inputDataModes.pdfMode && (!globalThis.imageAll["native"][n] || 
      (colorMode != "binary" && globalThis.imageAll["nativeColor"][n] != colorMode) ||
      rotate == false && globalThis.imageAll["nativeRotated"][n] == true) ? true : false;

    // In pdfMode the page is re-rendered from the pdf
    if (renderNativePDF) {

      globalThis.imageAll["nativeColor"][n] = "gray";
      globalThis.imageAll["nativeRotated"][n] = false;
      globalThis.imageAll["native"][n] = new Promise(async function (resolve, reject) {

        // Initialize scheduler if one does not already exist
        // This happens when the original scheduler is killed after all pages are rendered,
        // but then the user changes from color to grayscale (or vice versa).
        await initSchedulerIfNeeded("muPDFScheduler");

        const ms = await globalThis.muPDFScheduler;

        // Render to 300 dpi by default
        let dpi = 300;

        const imgWidthXml = globalThis.pageMetricsObj["dimsAll"][n][1];
        const imgWidthPdf = await ms.addJob('pageWidth', [n + 1, 300]);
        if (imgWidthPdf != imgWidthXml) {
          dpi = Math.round(300 * (imgWidthXml / imgWidthPdf));
        }

        const useColor = colorMode == "color" ? true : false;

        const res = await ms.addJob('drawPageAsPNG', [n + 1, dpi, useColor]);

        const image = document.createElement('img');
        await loadImage(res, image);

        resolve(image);

        // await displayImage(n, image);

      });
    }

    // Whether binarized image needs to be rendered
    const renderBinary = colorMode == "binary" && !globalThis.imageAll["binary"][n];

    // // Whether native image needs to be rendered
    // const renderNativeImage = colorMode == "gray" && globalThis.imageAll["nativeColor"][n] == "color";

    // Whether binarized image needs to be rotated (or re-rendered without rotation)
    const rotateBinary = colorMode == "binary" && (rotate == true && !globalThis.imageAll["binaryRotated"][n] && Math.abs(globalThis.pageMetricsObj["angleAll"][n]) > 0.05 || rotate == false && globalThis.imageAll["binaryRotated"][n] == true);

    // Whether native image needs to be rotated
    const rotateNative = colorName == "native" && (rotate == true && !globalThis.imageAll["nativeRotated"][n] && Math.abs(globalThis.pageMetricsObj["angleAll"][n]) > 0.05);

    // If nothing needs to be done, return early.
    if (!(renderBinary || rotateBinary || rotateNative )) return;

    // If no preference is specified for rotation, default to true
    const angleArg = rotate != false ? globalThis.pageMetricsObj["angleAll"][n] * (Math.PI / 180) * -1 || 0 : 0;

    const saveBinaryImageArg = "true";
    const saveColorImageArg = rotateNative ? "true" : "false";  

    const resPromise = (async () => {

      // Wait for non-rotated version before replacing with promise
      const inputImage = await Promise.resolve(globalThis.imageAll["native"][n]);

      const bs = await getBinaryScheduler();

      return bs.addJob("threshold", inputImage.src, { angle: angleArg }, { debug_file: "/debug.txt", max_page_gradient_recognize: "100", scribe_save_binary_rotated_image : saveBinaryImageArg, scribe_save_original_rotated_image: saveColorImageArg});

    })();

    if(saveColorImageArg == "true"){
      globalThis.imageAll["nativeRotated"][n] = Boolean(angleArg);
      globalThis.imageAll["native"][n] = resPromise.then(async (res) => {
        const image = document.createElement('img');
        await loadImage(res.data.imageOriginal, image);
        // displayImage(n, image, false);
        return(image);
      });  
    }

    if(saveBinaryImageArg == "true") {
      globalThis.imageAll["binaryRotated"][n] = Boolean(angleArg);
      globalThis.imageAll["binary"][n] = resPromise.then(async (res) => {
        const image = document.createElement('img');
        await loadImage(res.data.imageBinary, image);
        // displayImage(n, image, true);
        return(image);
      });
    }
  }));

}


// Function that handles page-level info for rendering to canvas and pdf
export async function renderPageQueue(n, mode = "screen", loadXML = true, lineMode = false, dimsLimit = null) {

  // Return if data is not loaded yet
  const imageMissing = inputDataModes.imageMode && (globalThis.imageAll["native"].length == 0 || globalThis.imageAll["native"][n] == null) || inputDataModes.pdfMode && (typeof (globalThis.muPDFScheduler) == "undefined");
  const xmlMissing = globalThis.hocrCurrent.length == 0 || typeof (globalThis.hocrCurrent[n]) != "string";
  if (imageMissing && (inputDataModes.imageMode || inputDataModes.pdfMode) || xmlMissing && inputDataModes.xmlMode[n]) {
    console.log("Exiting renderPageQueue early");
    return;
  }

  // Parse the relevant XML (relevant for both Canvas and PDF)
  if (loadXML && inputDataModes.xmlMode[n] && globalThis.hocrCurrent[n]) {
    currentPage.xmlDoc = parser.parseFromString(globalThis.hocrCurrent[n], "text/xml");
  } else if (!inputDataModes.xmlMode[n]) {
    currentPage.xmlDoc = null;
  }

  // Determine image size and canvas size
  let imgDims = null;
  let canvasDims = null;

  imgDims = new Array(2);
  canvasDims = new Array(2);

  // Get image dimensions from OCR data if present; otherwise get dimensions of images directly
  if (inputDataModes.xmlMode[n] || inputDataModes.pdfMode) {
    imgDims[1] = globalThis.pageMetricsObj["dimsAll"][n][1];
    imgDims[0] = globalThis.pageMetricsObj["dimsAll"][n][0];
  } else {
    const backgroundImage = await globalThis.imageAll["native"][n];
    imgDims[1] = backgroundImage.width;
    imgDims[0] = backgroundImage.height;
  }

  // The canvas size and image size are generally the same.
  // The exception is when rendering a pdf with the "standardize page size" option on,
  // which will scale the canvas size but not the image size.
  if (mode == "pdf" && dimsLimit[0] > 0 && dimsLimit[1] > 0) {
    canvasDims[1] = dimsLimit[1];
    canvasDims[0] = dimsLimit[0];
  } else {
    canvasDims[1] = imgDims[1];
    canvasDims[0] = imgDims[0];
  }


  currentPage.backgroundOpts.originX = "center";
  currentPage.backgroundOpts.originY = "center";

  currentPage.backgroundOpts.left = imgDims[1] * 0.5;
  currentPage.backgroundOpts.top = imgDims[0] * 0.5;


  let marginPx = Math.round(canvasDims[1] * leftGlobal);
  currentPage.backgroundOpts.angle = globalThis.pageMetricsObj["angleAll"][n] * -1 ?? 0;

  currentPage.backgroundOpts.left = imgDims[1] * 0.5;

  globalThis.doc.addPage({ size: [canvasDims[1], canvasDims[0]], margin: 0 });
  const backgroundImage = await Promise.resolve(globalThis.imageAll["native"][n]);
  globalThis.doc.image(backgroundImage.src, (currentPage.leftAdjX || 0), 0, { align: 'left', valign: 'top' });

  await renderPage(canvas, globalThis.doc, currentPage.xmlDoc, "pdf", globalSettings.defaultFont, lineMode, imgDims, canvasDims, globalThis.pageMetricsObj["angleAll"][n], inputDataModes.pdfMode, globalThis.fontObj, currentPage.leftAdjX);

}


async function getBinaryScheduler() {
  // Initialize scheduler if one does not already exist
  if(!globalThis.binaryScheduler) {
    const n = Math.min(Math.ceil(globalThis.imageAll["native"].length / 4), 4);
    console.log("Creating new Tesseract scheduler with " + n + " workers.")
    globalThis.binaryScheduler = createTesseractScheduler(n);
  }
  return(globalThis.binaryScheduler)
}

window["binarySchedulerInit"] = async function () {
  // Workers take a non-trivial amount of time to started so a tradeoff exists with how many to use.
  // Using 1 scheduler per 4 pages as a quick fix--have not benchmarked optimal number.
  const n = Math.min(Math.ceil(globalThis.imageAll["native"].length / 4), 4);
  return await createTesseractScheduler(n);
}

async function createTesseractScheduler(workerN, config = null) {

  const allConfig = config || getTesseractConfigs();

  const workerOptions = { corePath: './tess/tesseract-core.wasm.js', workerPath: './tess/worker.min.js', langPath: "./tess/lang" };

  const scheduler = await Tesseract.createScheduler();

  scheduler["workers"] = [];
  for (let i = 0; i < workerN; i++) {
    const w = Tesseract.createWorker(workerOptions);
    await w.load();
    await w.loadLanguage('eng');
    await w.initialize('eng', allConfig.tessedit_ocr_engine_mode);
    await w.setParameters(allConfig);
    scheduler["workers"][i] = w;

    scheduler.addWorker(w);
  }

  // Add config object to scheduler.
  // This does not do anything directly, but allows for easily checking what options were used at a later point.
  scheduler["config"] = allConfig;

  return (scheduler);

}

function getTesseractConfigs() {
  // Get current settings as specified by user
  const oemConfig = "TESSERACT_ONLY";
  const psmConfig = "AUTO";

  const allConfig = {
    tessedit_ocr_engine_mode: oemConfig,
    tessedit_pageseg_mode: psmConfig,
    hocr_char_boxes: '1',
    // The Tesseract LSTM engine frequently identifies a bar character "|"
    // This is virtually always a false positive (usually "I").
    tessedit_char_blacklist: "|ﬁﬂéï",
    debug_file: "/debug.txt",
    max_page_gradient_recognize: "100",
    hocr_font_info: "1"
  };

  return (allConfig);
}

// Checks scheduler to see if user has changed settings since scheduler was created
function checkTesseractScheduler(scheduler, config = null) {
  if (!scheduler?.["config"]) return false;
  const allConfig = config || getTesseractConfigs();
  delete scheduler?.["config"].rectangle;

  if (JSON.stringify(scheduler.config) === JSON.stringify(allConfig)) return true;
  return false;

}



window["muPDFSchedulerInit"] = async function () {
  await initMuPDFScheduler(globalThis.pdfFile, 3);
  if (globalThis.imageAll["native"]) {
    // TODO: Fix to work with promises
    window["muPDFScheduler"]["pngRenderCount"] = 0;
  } else {
    window["muPDFScheduler"]["pngRenderCount"] = 0;
  }

  return;
}

// Function that is invoked before a scheduler is used.
// If the scheduler already exists, resolves immediately.
// If scheduler is being created already, return promise that resolves when that is done.
// If scheduler does not exist and is not being created, initialize and return promise that resolves when done.
async function initSchedulerIfNeeded(x) {

  if(!window[x]){
    window[x] = window[x + "Init"]();
  }
  return(window[x]);
}

async function renderPDF() {

  globalThis.doc = new PDFDocument({
    margin: 0,
    autoFirstPage: false
  });

  globalThis.stream = globalThis.doc.pipe(blobStream());

  globalThis.stream.on('finish', function () {
    // get a blob you can do whatever you like with

    // Note: Do not specify pdf MIME type.
    // Due to a recent Firefox update, this causes the .pdf to be opened in the same tab (replacing the main site)
    // https://support.mozilla.org/en-US/kb/manage-downloads-preferences-using-downloads-menu

    //let url = stream.toBlobURL('application/pdf');
    globalThis.downloadBlob = globalThis.stream.toBlobURL();
    let fileName = globalThis.downloadFileName.replace(/\.\w{1,4}$/, "") + ".pdf";

    globalThis.saveAs(globalThis.downloadBlob, fileName);

  });

  let fontObjData = new Object;
  //TODO: Edit so that only fonts used in the document are inserted into the PDF.
  for (const [familyKey, familyObj] of Object.entries(globalThis.fontObj)) {
    if (typeof (fontObjData[familyKey]) == "undefined") {
      fontObjData[familyKey] = new Object;
    }

    for (const [key, value] of Object.entries(familyObj)) {

      if (key == "small-caps") {
        //Note: pdfkit has a bug where fonts with spaces in the name create corrupted files (they open in browser but not Adobe products)
        //Taking all spaces out of font names as a quick fix--this can likely be removed down the line if patched.
        //https://github.com/foliojs/pdfkit/issues/1314

        const fontObjI = await globalThis.fontObj[familyKey][key];

        fontObjI.tables.name.postScriptName["en"] = globalSettings.defaultFont + "-SmallCaps";
        fontObjI.tables.name.fontSubfamily["en"] = "SmallCaps";
        fontObjI.tables.name.postScriptName["en"] = fontObjI.tables.name.postScriptName["en"].replaceAll(/\s+/g, "");

        fontObjData[familyKey][key] = fontObjI.toArrayBuffer();
      } else if (key == "normal" ) {
        fontObjData[familyKey][key] = fontDataOptimized?.[familyKey]?.["normal"];
      } else if (key == "italic"  ) {
        fontObjData[familyKey][key] = fontDataOptimized?.[familyKey]?.["italic"];
      } else {
        const fontObjI = await globalThis.fontObj[familyKey][key];
        fontObjI.tables.name.postScriptName["en"] = fontObjI.tables.name.postScriptName["en"].replaceAll(/\s+/g, "");
        fontObjData[familyKey][key] = fontObjI.toArrayBuffer();
      }

      if(fontObjData[familyKey][key]) {
        globalThis.doc.registerFont(familyKey + "-" + key, fontObjData[familyKey][key]);
      }
    }
  }


  let minValue = parseInt(1);
  let maxValue = parseInt(globalThis.imageAll.native.length);

  let pagesArr = [...Array(maxValue - minValue + 1).keys()].map(i => i + minValue - 1);

  // Render all pages to PNG
  if (inputDataModes.pdfMode) {

    // TODO: Fix to work with promises
    const pngRenderCount = 0;
    if (pngRenderCount < globalThis.imageAll["native"].length) {

      await initSchedulerIfNeeded("muPDFScheduler");

    }
  }

  await renderPDFImageCache(pagesArr, true);


  let standardizeSizeMode = false;
  let dimsLimit = new Array(maxValue - minValue + 1);
  dimsLimit.fill(0);
  if (standardizeSizeMode) {
    for (let i = (minValue - 1); i < maxValue; i++) {
      dimsLimit[0] = Math.max(dimsLimit[0], globalThis.pageMetricsObj["dimsAll"][i][0]);
      dimsLimit[1] = Math.max(dimsLimit[1], globalThis.pageMetricsObj["dimsAll"][i][1]);
    }
  }

  for (let i = (minValue - 1); i < maxValue; i++) {

    await renderPageQueue(i, "pdf", true, false, dimsLimit);

  }

  globalThis.doc.end();
  
}

// Modified version of code found in FileSaver.js
globalThis.saveAs = function(blob, name, opts) {
  var a = document.createElement('a');
  name = name || blob.name || 'download';
  a.download = name;
  //a.rel = 'noopener'; // tabnabbing
  // TODO: detect chrome extensions & packaged apps
  // a.target = '_blank'
  if (typeof blob === 'string') {
    a.href = blob;
  } else {
    a.href = globalThis.URL.createObjectURL(blob);
  }
  a.dispatchEvent(new MouseEvent('click', {
    bubbles: true,
    cancelable: true,
    view: window
  }));
}


// TODO: Rework storage of optimized vs. non-optimized fonts to be more organized
// var fontDataOptimized, fontDataOptimizedItalic, fontDataOptimizedSmallCaps;

var fontDataOptimized = {};

export async function optimizeFont2(fontFamily) {

  const fontMetricI = globalSettings.multiFontMode ? globalThis.fontMetricsObj[fontFamily] : globalThis.fontMetricsObj["Default"];
  
  if(!fontMetricI) return;

  const fontNormal = await globalThis.fontObj[fontFamily]["normal"];
  const fontItalic = await globalThis.fontObj[fontFamily]["italic"];

  fontNormal.tables.gsub = null;
  fontItalic.tables.gsub = null;

  // Quick fix due to bug in pdfkit (see note in renderPDF function)
  fontNormal.tables.name.postScriptName["en"] = fontNormal.tables.name.postScriptName["en"].replaceAll(/\s+/g, "");

  // Italic fonts can be optimized in 2 ways.  If metrics exist for italics, then they are optimized using those (similar to normal fonts).
  // If no metrics exist for italics, then a subset of optimizations are applied using metrics from the normal variant. 
  const fontAuxArg = fontMetricI["italic"] ? null : fontItalic;
  let fontArr = await optimizeFont(fontNormal, fontAuxArg, fontMetricI["normal"]);

  if(!fontDataOptimized[fontFamily]){
    fontDataOptimized[fontFamily] = {};
  }

  fontDataOptimized[fontFamily]["normal"] = fontArr[0].toArrayBuffer();
  globalThis.fontObj[fontFamily]["normal"] = loadFont(fontFamily, fontDataOptimized[fontFamily]["normal"], true);
  await loadFontBrowser(fontFamily, "normal", fontDataOptimized[fontFamily]["normal"], true);

  if (!fontMetricI["italic"]) {
    fontDataOptimized[fontFamily]["italic"] = fontArr[1].toArrayBuffer();
    globalThis.fontObj[fontFamily]["italic"] = loadFont(fontFamily + "-italic", fontDataOptimized[fontFamily]["italic"], true);
    await loadFontBrowser(fontFamily, "italic", fontDataOptimized[fontFamily]["italic"], true);
  }

  // Create small caps font using optimized "normal" font as a starting point
  //createSmallCapsFont(globalThis.fontObj["Libre Baskerville"]["normal"], "Libre Baskerville", fontMetricsObj["heightSmallCaps"] || 1, fontMetricsObj);

  // Optimize small caps if metrics exist to do so
  if (fontMetricI["small-caps"]) {
    fontArr = await optimizeFont(globalThis.fontObj[fontFamily]["small-caps"], null, fontMetricI["small-caps"]);
    fontDataOptimized[fontFamily]["small-caps"] = fontArr[0].toArrayBuffer();
    const kerningPairs = JSON.parse(JSON.stringify(fontArr[0].kerningPairs));
    globalThis.fontObj[fontFamily]["small-caps"] = loadFont(fontFamily + "-small-caps", fontDataOptimized[fontFamily]["small-caps"], true);
    await loadFontBrowser(fontFamily, "small-caps", fontDataOptimized[fontFamily]["small-caps"], true);
    // TODO: Fix to re-apply kerning pairs while running async
    const smallCapsFont = await globalThis.fontObj[fontFamily]["small-caps"];
    smallCapsFont.kerningPairs = kerningPairs;
    // globalThis.fontObj[fontFamily]["small-caps"].kerningPairs = kerningPairs;
  }

  // Optimize italics if metrics exist to do so
  if (fontMetricI["italic"]) {
    fontArr = await optimizeFont(fontItalic, null, fontMetricI["italic"], "italic");
    fontDataOptimized[fontFamily]["italic"] = fontArr[0].toArrayBuffer();
    globalThis.fontObj[fontFamily]["italic"] = loadFont(fontFamily + "-italic", fontDataOptimized[fontFamily]["italic"], true);
    await loadFontBrowser(fontFamily, "italic", fontDataOptimized[fontFamily]["italic"], true);
  }


}


var convertPageWorker = new Worker('js/convertPage.js');
convertPageWorker.promises = {};
convertPageWorker.promiseId = 0;


// Input array contents:
// [0] HOCR data
// [1] Page number
// [2] Abbyy mode
// [3] Object with arbitrary values to pass through to result
function convertPage(args) {

  if (args.length == 3) {
    args.push({});
  }

  return new Promise(function (resolve, reject) {
    let id = convertPageWorker.promiseId++;
    convertPageWorker.promises[id] = { resolve: resolve };

    args.push(id);

    convertPageWorker.postMessage(args);

  });

}

// Function for updating the import/recognition progress bar, and running functions after all data is loaded. 
// Should be called after every .hocr page is loaded (whether using the internal engine or uploading data),
// as well as after every image is loaded (not including .pdfs). 
async function updateDataProgress(mainData = true) {


  loadCountHOCR = loadCountHOCR + 1;

  const valueMax = globalThis.imageAll.native.length;

  // Update progress bar between every 1 and 5 iterations (depending on how many pages are being processed).
  // This can make the interface less jittery compared to updating after every loop.
  // The jitter issue will likely be solved if more work can be offloaded from the main thread and onto workers.
  const updateInterval = Math.min(Math.ceil(valueMax / 10), 5);
  if (loadCountHOCR % updateInterval == 0 || loadCountHOCR == valueMax) {
    if (loadCountHOCR == valueMax) {

      globalThis.fontMetricsObj = calculateOverallFontMetrics(fontMetricObjsMessage);

      calculateOverallPageMetrics();

      let defaultFontObs = 0;
      let namedFontObs = 0;
      if (globalThis.fontMetricsObj["Default"]?.obs) {defaultFontObs = defaultFontObs + globalThis.fontMetricsObj["Default"]?.obs};
      if (globalThis.fontMetricsObj["Libre Baskerville"]?.obs) {namedFontObs = namedFontObs + globalThis.fontMetricsObj["Libre Baskerville"]?.obs};
      if (globalThis.fontMetricsObj["Open Sans"]?.obs) {namedFontObs = namedFontObs + globalThis.fontMetricsObj["Open Sans"]?.obs};

      globalSettings.multiFontMode = namedFontObs > defaultFontObs ? true : false;

      // When we have metrics for individual fonts families, those are used to optimize the appropriate fonts.
      // Otherwise, the "default" metric is applied to whatever font the user has selected as the default font. 
      const metricsFontFamilies = Object.keys(globalThis.fontMetricsObj);
      // const multiFontMode = metricsFontFamilies.includes("Libre Baskerville") || metricsFontFamilies.includes("Open Sans");
      const optFontFamilies = globalSettings.multiFontMode ? metricsFontFamilies.filter((x) => x != "Default") : [globalSettings.defaultFont];

      for (let family of optFontFamilies) {
        await optimizeFont2(family);
      }

      renderPDF();
    }
  }
}



convertPageWorker.onmessage = function (e) {

  const n = e.data[1];
  const argsObj = e.data[2];

  const oemCurrent = !argsObj["engine"] || argsObj["mode"] != "full" || argsObj["engine"] == document.getElementById("displayLabelText").innerHTML ? true : false;

  // If an OEM engine is specified, save to the appropriate object within hocrAll,
  // and only set to hocrCurrent if appropriate.  This prevents "Recognize All" from
  // overwriting the wrong output if a user switches hocrCurrent to another OCR engine
  // while the recognition job is running.
  if (argsObj["engine"] && argsObj["mode"] == "full") {
    globalThis.hocrAll[argsObj["engine"]][n] = e.data[0][0] || "<div class='ocr_page'></div>";
    if (oemCurrent) {
      globalThis.hocrCurrent[n] = e.data[0][0] || "<div class='ocr_page'></div>";
    }
  } else {
    globalThis.hocrCurrent[n] = e.data[0][0] || "<div class='ocr_page'></div>";
  }

  // When using the "Recognize Area" feature the XML dimensions will be smaller than the page dimensions
  if (argsObj["mode"] == "area") {
    globalThis.pageMetricsObj["dimsAll"][n] = [currentPage.backgroundImage.height, currentPage.backgroundImage.width];
    globalThis.hocrCurrent[n] = globalThis.hocrCurrent[n].replace(/bbox( \d+)+/, "bbox 0 0 " + currentPage.backgroundImage.width + " " + currentPage.backgroundImage.height);
  } else {
    globalThis.pageMetricsObj["dimsAll"][n] = e.data[0][1];
  }

  inputDataModes.xmlMode[n] = true;

  globalThis.pageMetricsObj["angleAll"][n] = e.data[0][2];
  globalThis.pageMetricsObj["leftAll"][n] = e.data[0][3];
  globalThis.pageMetricsObj["angleAdjAll"][n] = e.data[0][4];

  fontMetricObjsMessage[n] = e.data[0][5];

  convertPageWorker.promises[e.data[e.data.length - 1]].resolve();

}

function calculateOverallPageMetrics() {
  // It is possible for image resolution to vary page-to-page, so the left margin must be calculated
  // as a percent to remain visually identical between pages.
  let leftAllPer = new Array(globalThis.pageMetricsObj["leftAll"].length);
  for (let i = 0; i < globalThis.pageMetricsObj["leftAll"].length; i++) {
    leftAllPer[i] = globalThis.pageMetricsObj["leftAll"][i] / globalThis.pageMetricsObj["dimsAll"][i][1];
  }
  leftGlobal = quantile(leftAllPer, 0.5);
  globalThis.pageMetricsObj["manAdjAll"] = new Array(globalThis.pageMetricsObj["leftAll"].length);
  globalThis.pageMetricsObj["manAdjAll"].fill(0);

}

