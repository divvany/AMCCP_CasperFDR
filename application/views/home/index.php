<div class="content-wrapper">


    <section class="content-header">

        <h1>

            Casper & FDR


        </h1>

        <ol class="breadcrumb">

            <li><a href="<?= base_url(); ?>"><i class="fa fa-dashboard"></i> Home </a></li>

        </ol>

    </section>

    <section class="content">

        <div class="row">


            <div class="col-md-7">


                <div class="box box-primary">


                    <div class="box-header">
                        <h3 class="box-title"><span id="theWord">The</span> <label id="fileName"
                                                                                   class="fileNameSize"></label>
                            <span id="splWord">.spl file</span>
                            <small>Edit file</small>
                        </h3>


                        <button id="button" type="button" name="downFile" onclick="saveTextAsFile()"
                                class="btn btn-small btn-primary pull-right">
                            &nbsp; Save
                            this file &nbsp;&nbsp;
                        </button>


                    </div>

                    <!--                    --><?php //echo form_close(); ?>


                    <div class="box-body pad">

                        <div class="form-group">


                            <textarea id="textArea" name="fileContent" class="textAreaStyle" srequired
                                      placeholder="Usage:&#10; - Select a file from Casper library (or open your own custom file)&#10; - Edit the file as needed or write it directly here&#10; - Press 'Check protocol'"
                                      style="width: 100%; height:310px; font-size: 14px; line-height: 18px; border: 1px solid #dddddd; padding: 10px;"></textarea>


                        </div>

                    </div>

                    <div class="box-footer">

                        <button id="buttonCheckProtocol" name="checkProtocol"
                                class="btn btn-primary btn-small pull-right" onclick="checkProtocol()">
                            Check
                            protocol
                        </button>

                        <span class="pull-right">&nbsp;  &nbsp;  &nbsp; </span>

                        <button type="button" class="btn btn-primary pull-right" data-toggle="modal"
                                data-target="#modal-reprez" onclick="representProtocol()">
                            Represent protocol
                        </button>


                        <div class="modal fade" id="modal-reprez">


                            <div class="modal-dialog">

                                <div class="modal-content">

                                    <div class="modal-header">

                                        <h3 style="color: #1d5da8" class="modal-title">


                                            Protocol representation</h3>


                                    </div>


                                    <div class="modal-body">

                                        <canvas id="protocol-desc" title="Right click to save the image"
                                                style="border:0px solid;background-color:white">Your web browser does
                                            not supports HTML5!
                                        </canvas>

                                    </div>


                                    <div class="modal-footer ">
                                        <button type="button" class="btn btn-primary pull-right" data-dismiss="modal"
                                                aria-label="Close">
                                            &nbsp;&nbsp; Close &nbsp;&nbsp;&nbsp;
                                        </button>

                                    </div>


                                </div>
                            </div>
                        </div>


                        <input onchange="addTextFromFile()" id="myFile" type="file" name="fileLoaded"/>


                    </div>


                </div>
            </div>


            <div class="col-md-5">


                <div class="box box-primary">


                    <div class="box-header with-border">

                        <h3 class="box-title">Choose a file from Casper examples library:</h3>


                    </div>
                    <div class="box-body">


                        <div class="row">

                            <?php

                            function print_files($item, $key, $key_first)
                            {
                                if (!is_array($item)) {

                                    if ((strpos($item, '.spl') !== false) && (strpos($item, '~') == false)) {

                                        ?>
                                        <option onclick="addText('<?= $key_first; ?>','<?= $item; ?>');"
                                                value="<?= $key_first . $item; ?>"> <?= $item; ?></option>

                                        <?php

                                    }
                                } else {
                                    ?>
                                    <optgroup label="<?= substr($key, 0, -1); ?>">

                                        <!--                                        --><?php //array_walk_recursive($item, 'print_files',$key); ?>

                                        <?php
                                        foreach ($item as $file) {

                                            $folder = $key_first . $key;

                                            if ((strpos($file, '.spl') !== false) && (strpos($file, '~') == false)) {

                                                ?>
                                                <option onclick="addText('<?= $folder; ?>','<?= $file; ?>')"
                                                        value="<?= $folder . $file; ?>"> <?= $file; ?></option>

                                                <?php
                                            }

                                        }

                                        ?>
                                    </optgroup>

                                    <?php
                                }

                            }

                            foreach ($folders as $key => $item) {
                                ?>

                                <div class="col-md-6">


                                    <select name="filename" class="select_design">
                                        <option style="font-weight: bold" selected disabled
                                                value="<?= substr($key, 0, -1); ?>"><b> <?= substr($key, 0, -1); ?></b>
                                        </option>

                                        <?php
                                        asort($item);
                                        array_walk($item, 'print_files', $key);
                                        ?>

                                    </select>

                                </div>

                                <?php


                            }
                            ?>

                        </div>


                        <br>

                        <button class="btn btn-primary btn-block" onclick="checkProtocolFromLibrary()">Check protocol
                            from
                            library
                        </button>


                    </div>

                </div>


            </div>


        </div>


    </section>

</div>


<script type="text/javascript">

    var file_name = '';
    var file_path = '';
    var textArea = document.getElementById("textArea");
    var selectedFile = false;

    var file_n = 'file.spl';

    jQuery.ajax({
        type: "POST",
        data: {file_n: file_n},
        url: "<?php echo base_url() . "home/setFileName"; ?>"


    });


    var protocolAgents = [];
    var protocolFreeVars = [];
    var protocolDescription = [];

    var freeVars = [];
    var agentNames = [];
    var bobFlag = true;


    var blackColor = "#050006";
    var blueColor = "#1d5da8";


    var originalIntruderName = "";
    var intruderName = "";

    function parseInputFileSyntax() {

        var dictionary = ["Free variables", "Freevariables", "Processes", "Protocol description", "Protocoldescription", "Specification", "Actual variables", "Actualvariables", "Functions", "System", "Intruder Information", "IntruderInformation", "Inlinefunctions", "Inline functions", "Equivalences", "Preamble", "Channels"];

        var dictionary_flag = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];


        var protocolBody = textArea.value;


        var tokens = protocolBody.split("#");

        var ok = true;


        for (i = 1; i < tokens.length; i++) {

            var tag = tokens[i].split("\n");
            var index = dictionary.indexOf(tag[0].trim());
            if (index === -1) {
                alert("Tag \"#" + tag[0] + "\" is not recognized by Casper syntax!\n Please review the file!");
                ok = false;
            }
            else {

                dictionary_flag[index] = 1;
            }

        }

        var number_of_tags = 0;

        for (i = 0; i < dictionary_flag.length; i++) {

            if (dictionary_flag[i] === 1)
                number_of_tags++;

        }

        if (number_of_tags < 8) {
            alert("The file does't have enough tags to be compiled with Casper!\n Please review the file!");
            ok = false;
        }

        return ok;
    }


    function getProtocolInfo(fileContent) {


        if (fileContent.includes("#Free variables")) {
            var protocolTokens = fileContent.split("#Free variables");
        }

        if (fileContent.includes("#Freevariables")) {
            var protocolTokens = fileContent.split("#Freevariables");
        }


        var freeVariables = protocolTokens[1].split("#");


        var protocolVariables = freeVariables[0].trim();

        var tokens = protocolVariables.split("\n");


        var free_vars = "";

        for (i = 0; i < tokens.length; i++) {

            free_vars += tokens[i] + "*";

        }


        protocolFreeVars = free_vars.split("*");


        jQuery.ajax({
            type: "POST",
            data: {free_vars: free_vars},
            url: "<?php echo base_url() . "checkProtocol/getFreeVariables"; ?>"

        });


        if (fileContent.includes("#Actual variables")) {
            protocolTokens = fileContent.split("#Actual variables");
        }

        if (fileContent.includes("#Actualvariables")) {
            protocolTokens = fileContent.split("#Actualvariables");
        }


        var actualVariables = protocolTokens[1].split("#");


        var protAgents = actualVariables[0].trim();

        tokens = protAgents.split("\n");


        var agents = "";

        for (i = 0; i < tokens.length; i++) {

            agents += tokens[i] + "*";

        }


        if (protocolTokens[1].includes("#Intruder Information")) {
            var intruder = protocolTokens[1].split("#Intruder Information");
        }

        if (protocolTokens[1].includes("#IntruderInformation")) {
            var intruder = protocolTokens[1].split("#IntruderInformation");
        }


        intruderName = intruder[1].split("IntruderKnowledge");

        agents += "*";
        agents += intruderName[0].trim();


        protocolAgents = agents.split("*");


        jQuery.ajax({
            type: "POST",
            data: {agents: agents},
            url: "<?php echo base_url() . "checkProtocol/getActualVariables"; ?>"


        });


        if (fileContent.includes("#Protocol description")) {
            protocolTokens = fileContent.split("#Protocol description");
        }

        if (fileContent.includes("#Protocoldescription")) {
            protocolTokens = fileContent.split("#Protocoldescription");
        }


        var protDescription = protocolTokens[1].split("#");

        var descLines = protDescription[0].trim();

        tokens = descLines.split('\n');


        var description = "";


        for (i = 0; i < tokens.length; i++) {

            description += tokens[i] + "*";

        }

        protocolDescription = description.split("*");


        jQuery.ajax({
            type: "POST",
            data: {description: description},
            url: "<?php echo base_url() . "checkProtocol/getProtocolDescription"; ?>"


        });


        protocolTokens = fileContent.split("#Specification");

        var protocolSpecification = protocolTokens[1].split("#");


        var specLines = protocolSpecification[0].trim();

        tokens = specLines.split('\n');

        var specification = "";


        for (i = 0; i < tokens.length; i++) {

            if (tokens[i].includes("--") === false) {

                specification += tokens[i] + "*";
            }

        }


        jQuery.ajax({
            type: "POST",
            data: {specification: specification},
            url: "<?php echo base_url() . "checkProtocol/getProtocolSpecification"; ?>"


        });


        originalIntruderName = protocolAgents[protocolAgents.length - 1].split("=")[1].trim();
        intruderName = "";

        if ((originalIntruderName.includes("M")) && (originalIntruderName.length === 1)) {

            intruderName = "Mallory";
        }

        if ((originalIntruderName.includes("I")) && (originalIntruderName.length === 1)) {

            intruderName = "Intruder";
        }


        var agentsArray = "";

        var tokens = "";

        for (i = 0; i < protocolAgents.length; i++) {

            if (protocolAgents[i].includes(":")) {

                tokens = protocolAgents[i].split(":");
                if (tokens[1].trim().localeCompare("Agent") === 0) {

                    agentsArray += tokens[0];
                    agentsArray += ",";

                }

                if (tokens[1].trim().localeCompare("Server") === 0) {

                    agentsArray += tokens[0];


                }

                if (tokens[1].trim().localeCompare("Bank") === 0) {

                    agentsArray += tokens[0];
                    bobFlag = false;

                }


            }

        }


        var freeVarsArray = "";
        var auxAgentsArray = "";


        for (i = 0; i < protocolFreeVars.length; i++) {

            if (protocolFreeVars[i].includes(":")) {

                if (agentsArray.length === 0) {


                    tokens = protocolFreeVars[i].split(":");

                    freeVarsArray += tokens[0];
                    freeVarsArray += ",";
                    auxAgentsArray += tokens[1];
                    auxAgentsArray += ",";


                    if (i === 2) {
                        break;
                    }
                }
                else {

                    tokens = protocolFreeVars[i].split(":");
                    if (tokens[1].trim().localeCompare("Agent") === 0) {

                        freeVarsArray += tokens[0];
                        freeVarsArray += ",";

                    }

                    if (tokens[1].trim().localeCompare("Server") === 0) {

                        freeVarsArray += tokens[0];


                    }
                    if (tokens[1].trim().localeCompare("Bank") === 0) {

                        freeVarsArray += tokens[0];
                        bobFlag = false;
                    }


                }
            }
        }


        if (auxAgentsArray.length !== 0) {
            agentsArray = auxAgentsArray;
        }
        // alert(freeVarsArray);

        var items = freeVarsArray.split(",");


        for (i = 0; i < items.length; i++) {

            freeVars[i] = items[i].trim();

        }


        items = agentsArray.split(",");

        agentNames = [];

        for (i = 0; i < items.length; i++) {

            agentNames[i] = items[i].trim();

        }


    }

    function addText(folder, file) {


        path = "examples_library/";

        path += folder;
        path += file;
        file_name = file;

        $('#theWord').hide();
        $('#splWord').hide();

        $('#fileName').text(file);


        var rawFile = new XMLHttpRequest();
        rawFile.open("POST", path, true);
        rawFile.onreadystatechange = function () {
            if (rawFile.readyState === 4) {
                if (rawFile.status === 200 || rawFile.status == 0) {
                    var allText = rawFile.responseText;

                    textArea.value = allText;

                    getProtocolInfo(allText);

                }
            }
        }
        rawFile.send(null);


        var file_n = folder + file;
        file_path = file_n;

        jQuery.ajax({
            type: "POST",
            data: {file_n: file_n},
            url: "<?php echo base_url() . "home/setFileName"; ?>"


        });

        selectedFile = true;

    }


    function addTextFromFile() {


        $('#fileName').hide();
        $('#theWord').show();
        $('#splWord').show();
        var file = document.getElementById("myFile").files[0];


        var ext = file.name.substring(file.name.lastIndexOf('.') + 1);

        if (ext === "spl") {

            file_name = file.name;
            var reader = new FileReader();

            reader.onload = function (e) {

                textArea.value = e.target.result;

            };


            reader.readAsText(file);


            var file_n = file_name;

            jQuery.ajax({
                type: "POST",
                data: {file_n: file_n},
                url: "<?php echo base_url() . "home/setFileName"; ?>"

                // ,
                // error: function (error) {
                //
                //     alert("error");
                //
                // },
                //
                // success: function (response) {
                //
                //     alert("succ");
                // }

            });


        }
        else {
            alert("You can only upload .spl files!");
        }

        $('#fileName').text(file_name);

        $('#theWord').hide();
        $('#splWord').hide();
        $('#fileName').show();

    }


    function saveTextAsFile() {

        var content = '';

        content = textArea.value;

        var filename = file_name;

        if (file_name === '') {
            filename = 'file.spl';
        }


        var textFileAsBlob = '';

        if (content != '') {

            textFileAsBlob = new Blob([content], {type: 'text/plain'});

            var downloadLink = document.createElement("a");
            downloadLink.download = filename;
            downloadLink.innerHTML = "Download File";
            if (window.webkitURL != null) {

                downloadLink.href = window.webkitURL.createObjectURL(textFileAsBlob);
            }
            else {

                downloadLink.href = window.URL.createObjectURL(textFileAsBlob);

                downloadLink.style.display = "none";
                document.body.appendChild(downloadLink);
            }

            downloadLink.click();
        }
        else {
            alert("The textarea is emthy!");
        }
    }


    function checkProtocol() {


        var fileContent = textArea.value;


        if (fileContent.length !== 0) {


            if (parseInputFileSyntax()) {


                getProtocolInfo(fileContent);


                jQuery.ajax({

                    type: "POST",
                    url: "<?php echo base_url() . "home/checkProtocol"; ?>",
                    data: {fileContent: fileContent}


                });


                var file_n = "file.spl";

                jQuery.ajax({
                    type: "POST",
                    data: {file_n: file_n},
                    url: "<?php echo base_url() . "home/setFileName"; ?>"

                });


                window.location = "<?php echo base_url() . 'checkProtocol';?>";
            }

        }
        else {

            alert("Text area is emthy!\nThere is no file selected!\nYou have to fill the textarea with a protocol description.\nYou can select it from the Casper library, upload it from your computer or write it directly in the text area!");
        }
    }

    function checkProtocolFromLibrary() {

        if (selectedFile) {


            var fileName = file_path;


            jQuery.ajax({

                type: "POST",
                url: "<?php echo base_url() . "home/checkProtocolFromLibrary"; ?>",
                data: {fileName: fileName}

                // ,
                //
                // error: function (error) {
                //
                //     alert("error");
                //
                // },
                //
                // success: function (response) {
                //
                //     alert("succes");
                // }

            });

            window.location = "<?php echo base_url() . 'checkProtocol';?>";
        }
        else {

            alert("There is no file selected!\nYou have to fill the textarea with a protocol description.\nYou can select it from the Casper library, upload it from your computer or write it directly in the text area!");

        }

    }


    function representProtocol() {


        var fileContent = textArea.value;

        if (fileContent.length !== 0) {

            getProtocolInfo(fileContent);


            var canvas = document.getElementById('protocol-desc');

            var context = canvas.getContext('2d');
            context.lineWidth = 1;


            var nrOfVerticalArrows;


            if (freeVars[freeVars.length - 1].length === 0) {

                nrOfVerticalArrows = freeVars.length - 1;
            }
            else {

                nrOfVerticalArrows = freeVars.length;
            }


            var horizoltalArrowLength;

            if (nrOfVerticalArrows === 2) {
                horizoltalArrowLength = 230;
                canvas.width = 310;
                canvas.style.padding = "0px 0px 0px 24%";
            }
            else {
                canvas.style.padding = "0px 0px 0px 0px";
                horizoltalArrowLength = 250;
                canvas.width = 585;

            }


            var nrOfMessages = 0;


            for (i = 0; i < protocolDescription.length; i++) {

                if ((protocolDescription[i].includes(":")) && (protocolDescription[i].includes("->"))) {

                    var aux = protocolDescription[i].split(".")[1].split("->")[1].split(":")[0].trim();

                    if (aux !== "") {

                        nrOfMessages += 1;
                    }
                }

            }


            var verticalArrowLength = (nrOfMessages - 1) * 31;

            canvas.height = verticalArrowLength + 60;

            var xStart = 25;

            var yStart = 40;

            var arrowSize = 8;


            context.beginPath();
            context.font = "23px Arial";
            context.fillStyle = blackColor;


            for (i = 0; i < agentNames.length; i++) {

                if ((agentNames[i].localeCompare(originalIntruderName) !== 0) && (agentNames[i].localeCompare(intruderName) !== 0)) {

                    if (agentNames[i].localeCompare("A") === 0) {

                        context.fillText("Alice", (xStart + 10 - ("Alice".length * 9) / 2), 22);
                        xStart += horizoltalArrowLength;
                        continue;
                    }

                    if (agentNames[i].localeCompare("B") === 0) {

                        if (bobFlag) {

                            context.fillText("Bob", (xStart - ("Bob".length * 9) / 2), 22);

                        }
                        else {
                            context.fillText("Bank", (xStart - ("Bob".length * 9) / 2), 22);
                        }

                        xStart += horizoltalArrowLength;
                        continue;

                    }


                    if (agentNames[i].localeCompare("AuthenticationServer") === 0) {

                        context.fillText(agentNames[i], (xStart - 66 - (agentNames[i].length * 9) / 2), 22);

                    }
                    else {

                        context.fillText(agentNames[i], (xStart - (agentNames[i].length * 9) / 2), 22);
                    }


                    xStart += horizoltalArrowLength;

                }

            }

            xStart = 35;

            for (i = 0; i < nrOfVerticalArrows; i++) {

                drawVerticalArrow(context, xStart, yStart, arrowSize, verticalArrowLength, blackColor);
                xStart += horizoltalArrowLength;
            }

            xStart = 35;
            yStart = 53;


            for (i = 1; i < protocolDescription.length; i++) {

                if ((protocolDescription[i].includes(":")) && (protocolDescription[i].includes("->"))) {

                    var item = protocolDescription[i].split(":");

                    if (item.length === 2) {

                        var agents = item[0].split(".")[1].split("->");

                        if ((agents[0].trim().localeCompare(freeVars[0]) === 0) && (agents[1].trim().localeCompare(freeVars[1]) === 0)) {

                            drawHorizontalArrowRight(context, xStart, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                        }

                        if ((agents[0].trim().localeCompare(freeVars[1]) === 0) && (agents[1].trim().localeCompare(freeVars[0]) === 0)) {

                            drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                        }


                        if ((freeVars.length > 2) && (nrOfVerticalArrows === 3)) {

                            if ((agents[0].trim().localeCompare(freeVars[0]) === 0) && (agents[1].trim().localeCompare(freeVars[2]) === 0)) {

                                drawHorizontalArrowRight(context, xStart, yStart, arrowSize, 2 * horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(freeVars[2]) === 0) && (agents[1].trim().localeCompare(freeVars[0]) === 0)) {

                                drawHorizontalArrowLeft(context, xStart, yStart, arrowSize, 2 * horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(freeVars[1]) === 0) && (agents[1].trim().localeCompare(freeVars[2]) === 0)) {

                                drawHorizontalArrowRight(context, xStart + horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                            if ((agents[0].trim().localeCompare(freeVars[2]) === 0) && (agents[1].trim().localeCompare(freeVars[1]) === 0)) {

                                drawHorizontalArrowLeft(context, xStart + horizoltalArrowLength, yStart, arrowSize, horizoltalArrowLength, blackColor, item[1], blueColor);

                            }

                        }

                        yStart += 30;
                    }

                }

            }
        }
        else {

            alert("There is no file selected!\nYou have to fill the textarea with a protocol description.\nYou can select it from the Casper library, upload it from your computer or write it directly in the text area!");

        }


    }


    function drawVerticalArrow(context, xStart, yStart, size, length, color) {


        context.fillStyle = color;

        context.beginPath();

        context.moveTo(xStart - 1, yStart - size);
        context.lineTo(xStart + 1, yStart - size);
        context.lineTo(xStart + 1, yStart - (-length));
        context.lineTo(xStart + 5, yStart - (-length));
        context.lineTo(xStart, yStart - (-length - size));
        context.lineTo(xStart - 5, yStart - (-length));
        context.lineTo(xStart - 1, yStart - (-length));
        context.lineTo(xStart - 1, yStart - size);
        context.fill();

    }


    function drawHorizontalArrowRight(context, xStart, yStart, size, length, color, message, messageColor) {

        context.fillStyle = color;

        context.beginPath();

        context.moveTo(xStart, yStart);
        context.lineTo(xStart, yStart + 2);
        context.lineTo(xStart + length - size, yStart + 2);
        context.lineTo(xStart + length - size, yStart + 2 + 5);
        context.lineTo(xStart + length, yStart + 1);
        context.lineTo(xStart + length - size, yStart - 5);
        context.lineTo(xStart + length - size, yStart);
        context.lineTo(xStart, yStart);
        context.fill();

        if (message !== "") {

            context.beginPath();
            context.fillStyle = messageColor;
            context.font = "bold 12px Arial";

            context.fillText(message, xStart + (length - 29 - (5 * message.length)) / 2, yStart - 6);
        }


    }


    function drawHorizontalArrowLeft(context, xStart, yStart, size, length, color, message, messageColor) {

        context.fillStyle = color;

        context.beginPath();

        context.moveTo(xStart + length, yStart);
        context.lineTo(xStart + length, yStart + 2);
        context.lineTo(xStart + size, yStart + 2);
        context.lineTo(xStart + size, yStart + 2 + 5);
        context.lineTo(xStart, yStart + 1);
        context.lineTo(xStart + size, yStart - 5);
        context.lineTo(xStart + size, yStart);
        context.lineTo(xStart, yStart);
        context.fill();

        if (message !== "") {
            context.beginPath();
            context.fillStyle = messageColor;
            context.font = "bold 12px Arial";
            context.fillText(message, xStart + (length - 25 - (5 * message.length)) / 2, yStart - 6);
        }

    }


</script>

